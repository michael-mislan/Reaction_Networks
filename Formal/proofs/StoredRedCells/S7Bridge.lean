import proofs.StoredRedCells.FiniteCertificate
import proofs.StoredRedCells.S7Data.Definitions

/-! Sparse S7 certificate interface. Amounts/extents here are in integer-scaled
certificate units. Full source coverage, physical-unit conversion and the
complete cost must still be instantiated in the source application. -/
namespace StoredRedCells.S7Certificate
noncomputable section
open Finset

def matrixEntry (r : Column) (i : Fin 10411) : ℝ :=
  (r.terms.map (fun p => if p.1 = i.val then (p.2 : ℝ) else 0)).sum

theorem weighted_matrix (r : Column)
    (hidx : ∀ p ∈ r.terms, p.1 < 10411) :
    (∑ i : Fin 10411,
      (-(chemicalWeight i.val : ℝ) + (auxiliaryWeight i.val : ℝ)) * matrixEntry r i) =
      (weighted r : ℝ) := by
  have hi : ∀ p ∈ r.terms.map (fun p => (p.1, (p.2 : ℝ))), p.1 < 10411 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact hidx q hq
  have h := FiniteCertificate.weighted_nat_column
    (r.terms.map (fun p => (p.1, (p.2 : ℝ))))
    (fun i => -(chemicalWeight i : ℝ) + (auxiliaryWeight i : ℝ)) hi
  simpa [matrixEntry, weighted, List.map_map, Function.comp_def] using h

theorem column_identity (r : Column)
    (hidx : ∀ p ∈ r.terms, p.1 < 10411) :
    (r.objective : ℝ) =
      -(∑ i : Fin 10411, (chemicalWeight i.val : ℝ) * matrixEntry r i) +
      (∑ i : Fin 10411, (auxiliaryWeight i.val : ℝ) * matrixEntry r i) +
      (residual r : ℝ) := by
  have h := weighted_matrix r hidx
  simp_rw [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib] at h
  simp only [residual, Int.cast_sub]
  linarith

theorem chemical_weight_nonnegative (i : Nat) : (0 : ℝ) ≤ chemicalWeight i := by
  have h : (0 : ℤ) ≤ chemicalWeight i := by
    unfold chemicalWeight
    positivity
  exact_mod_cast h

theorem inventory_scaled {J : Type*} [Fintype J]
    (columns : J → Column) (v : J → ℝ) (x0 ell : Fin 10411 → ℝ) (T : ℝ)
    (hidx : ∀ j, ∀ p ∈ (columns j).terms, p.1 < 10411)
    (hT : 0 ≤ T)
    (hsupply : ∀ j, (0 : ℝ) ≤ (columns j).supply)
    (hfloor : ∀ i, (chemicalWeight i.val : ℝ) ≠ 0 →
      ell i ≤ x0 i + ∑ j, matrixEntry (columns j) i * v j)
    (haux : ∀ i, (auxiliaryWeight i.val : ℝ) ≠ 0 →
      ∑ j, matrixEntry (columns j) i * v j = 0)
    (hL : ∀ j, (columns j).lower * T ≤ v j)
    (hU : ∀ j, v j ≤ (columns j).upper * T) :
    (∑ j, ((columns j).objective : ℝ) * v j) ≤
      (∑ i, (chemicalWeight i.val : ℝ) * (x0 i - ell i)) +
      (∑ j, (cost (columns j) : ℝ)) * T +
      (∑ j, ((columns j).supply : ℝ) * max (-v j) 0) := by
  have hcol (j : J) : ((columns j).objective : ℝ) + (columns j).supply =
      -(∑ i : Fin 10411, (chemicalWeight i.val : ℝ) * matrixEntry (columns j) i) +
      (∑ i : Fin 10411, (auxiliaryWeight i.val : ℝ) * matrixEntry (columns j) i) +
      (shiftedResidual (columns j) : ℝ) := by
    have h := column_identity (columns j) (hidx j)
    simp only [shiftedResidual, Int.cast_add]
    linarith
  have h := FiniteCertificate.inventory_with_reverse_supplies
    (fun i j => matrixEntry (columns j) i)
    (fun i j => matrixEntry (columns j) i)
    (fun i : Fin 10411 => (chemicalWeight i.val : ℝ))
    (fun i : Fin 10411 => (auxiliaryWeight i.val : ℝ))
    (fun j => ((columns j).objective : ℝ))
    (fun j => ((columns j).supply : ℝ))
    (fun j => (shiftedResidual (columns j) : ℝ))
    (fun j => ((columns j).lower : ℝ))
    (fun j => ((columns j).upper : ℝ))
    v x0 ell T (fun i => chemical_weight_nonnegative i.val) hsupply hT hfloor haux hL hU hcol
  simpa [cost] using h

/-- Physical-unit conversion, derived from explicit species balances and
extent bounds. W,S,B are the positive weight, stoichiometry and bound scales. -/
theorem inventory_physical {J : Type*} [Fintype J]
    (columns : J → Column) (xi : J → ℝ) (x0 ell : Fin 10411 → ℝ)
    (T W S B : ℝ) (hW : 0 < W) (hS : 0 < S) (hB : 0 < B)
    (hidx : ∀ j, ∀ p ∈ (columns j).terms, p.1 < 10411)
    (hT : 0 ≤ T) (hsupply : ∀ j, (0 : ℝ) ≤ (columns j).supply)
    (hfloor : ∀ i, (chemicalWeight i.val : ℝ) ≠ 0 →
      ell i ≤ x0 i + ∑ j, (matrixEntry (columns j) i / S) * xi j)
    (haux : ∀ i, (auxiliaryWeight i.val : ℝ) ≠ 0 →
      ∑ j, (matrixEntry (columns j) i / S) * xi j = 0)
    (hL : ∀ j, ((columns j).lower : ℝ) / B * T ≤ xi j)
    (hU : ∀ j, xi j ≤ ((columns j).upper : ℝ) / B * T) :
    (∑ j, (((columns j).objective : ℝ) / (W*S)) * xi j) ≤
      (∑ i, ((chemicalWeight i.val : ℝ) / W) * (x0 i - ell i)) +
      ((∑ j, (cost (columns j) : ℝ)) / (W*S*B)) * T +
      (∑ j, (((columns j).supply : ℝ) / (W*S)) * max (-xi j) 0) := by
  have hSn : S ≠ 0 := ne_of_gt hS
  have hBn : B ≠ 0 := ne_of_gt hB
  have hWn : W ≠ 0 := ne_of_gt hW
  have hSB : 0 < S*B := mul_pos hS hB
  have hscale : 0 < W*S*B := mul_pos (mul_pos hW hS) hB
  have hrow (i : Fin 10411) :
      (∑ j, matrixEntry (columns j) i * (B*xi j)) =
        (S*B) * (∑ j, (matrixEntry (columns j) i / S) * xi j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have hf : ∀ i, (chemicalWeight i.val : ℝ) ≠ 0 →
      (S*B)*ell i ≤ (S*B)*x0 i + ∑ j, matrixEntry (columns j) i*(B*xi j) := by
    intro i hi
    rw [hrow]
    simpa only [mul_add] using
      mul_le_mul_of_nonneg_left (hfloor i hi) (le_of_lt hSB)
  have hb : ∀ i, (auxiliaryWeight i.val : ℝ) ≠ 0 →
      ∑ j, matrixEntry (columns j) i*(B*xi j) = 0 := by
    intro i hi
    rw [hrow, haux i hi, mul_zero]
  have hl : ∀ j, (columns j).lower*T ≤ B*xi j := by
    intro j
    calc
      ((columns j).lower : ℝ)*T = B*(((columns j).lower : ℝ)/B*T) := by
        field_simp
      _ ≤ B*xi j := mul_le_mul_of_nonneg_left (hL j) (le_of_lt hB)
  have hu : ∀ j, B*xi j ≤ (columns j).upper*T := by
    intro j
    calc
      B*xi j ≤ B*(((columns j).upper : ℝ)/B*T) :=
        mul_le_mul_of_nonneg_left (hU j) (le_of_lt hB)
      _ = ((columns j).upper : ℝ)*T := by
        field_simp
  have h := inventory_scaled columns (fun j => B*xi j)
    (fun i => (S*B)*x0 i) (fun i => (S*B)*ell i) T hidx hT hsupply hf hb hl hu
  have ho : (∑ j, ((columns j).objective : ℝ)*(B*xi j)) =
      (W*S*B)*(∑ j, (((columns j).objective : ℝ)/(W*S))*xi j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp
  have hw : (∑ i, (chemicalWeight i.val : ℝ)*((S*B)*x0 i-(S*B)*ell i)) =
      (W*S*B)*(∑ i, ((chemicalWeight i.val : ℝ)/W)*(x0 i-ell i)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have hm (j : J) : max (-(B*xi j)) 0 = B*max (-xi j) 0 := by
    by_cases hx : 0 ≤ xi j
    · rw [max_eq_right (neg_nonpos.mpr (mul_nonneg (le_of_lt hB) hx)),
        max_eq_right (neg_nonpos.mpr hx), mul_zero]
    · have hn : xi j ≤ 0 := le_of_not_ge hx
      rw [max_eq_left (neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hB) hn)),
        max_eq_left (neg_nonneg.mpr hn)]
      ring
  have hr : (∑ j, ((columns j).supply : ℝ)*max (-(B*xi j)) 0) =
      (W*S*B)*(∑ j, (((columns j).supply : ℝ)/(W*S))*max (-xi j) 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [hm]
    field_simp
  have hc : (∑ j, (cost (columns j) : ℝ))*T =
      (W*S*B)*(((∑ j, (cost (columns j) : ℝ))/(W*S*B))*T) := by
    field_simp
  rw [ho, hw, hc, hr] at h
  simp only [← mul_add] at h
  exact le_of_mul_le_mul_left h hscale

end
end StoredRedCells.S7Certificate
