import proofs.TypeIIStability.Witness

namespace TypeIIStability.Witness
noncomputable section
open scoped Matrix BigOperators

def eigenvector : Fin 7 → ℂ := fun i => (x i : ℂ) * ((u i : ℂ) + (v i : ℂ) * Complex.I)

theorem eigenvector_ne_zero : eigenvector ≠ 0 := by
  intro hz
  have hh := congrFun hz 6
  have hx := parameters_positive.2.2.2 6
  have hu : u 6 = 200 := rfl
  have hv : v 6 = 0 := rfl
  have hr := congrArg Complex.re hh
  norm_num [eigenvector, hu, hv] at hr
  linarith

theorem exact_eigenpair : DUnstableCores.HasEigenpair A (1 + 8 * Complex.I) eigenvector := by
  refine ⟨eigenvector_ne_zero, ?_⟩
  intro i
  have hx : ∀ j, x j ≠ 0 := fun j => ne_of_gt (parameters_positive.2.2.2 j)
  have hr := congrFun pencil_real i
  have hi := congrFun pencil_imag i
  have hterm : ∀ j, (A i j : ℂ) * eigenvector j =
      (H i j : ℂ) * ((u j : ℂ) + (v j : ℂ) * Complex.I) := by
    intro j
    dsimp [A, eigenvector]
    rw [Complex.ofReal_div]
    field_simp [hx j]
  change (∑ j, (A i j : ℂ) * eigenvector j) = _
  simp_rw [hterm]
  apply Complex.ext
  · simp [eigenvector, Complex.mul_re, Complex.mul_im] 
    dsimp [Matrix.mulVec, dotProduct] at hr hi
    linear_combination hr
  · simp [eigenvector, Complex.mul_re, Complex.mul_im]
    dsimp [Matrix.mulVec, dotProduct] at hr hi
    linear_combination hi

theorem unstable : DUnstableCores.HurwitzUnstable A := by
  refine ⟨1 + 8 * Complex.I, eigenvector, ?_, exact_eigenpair⟩
  norm_num

end
end TypeIIStability.Witness
