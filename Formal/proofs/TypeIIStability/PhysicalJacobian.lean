import proofs.TypeIIStability.Witness
import proofs.MixedDegradation.LogDrift

namespace TypeIIStability.Witness
noncomputable section
open scoped Matrix BigOperators
open MixedDegradation
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Products of the literal reactions A0 -> B0+B2, B0 -> C,
 A1 -> B1+B0, B1 -> A2, A2 -> B2+B1, B2 -> A0, C -> A1. -/
def products (z : Fin 7 → ℝ) : Fin 7 → ℝ :=
  ![z 1*z 5, z 6, z 3*z 1, z 4, z 5*z 3, z 0, z 2]

def normalize : (Fin 7 → ℝ) →L[ℝ] (Fin 7 → ℝ) :=
  matrixCLM (Matrix.diagonal (fun i => 1 / x i))

def forwardRate (i : Fin 7) : ℝ := p i / x i
def reverseRate (i : Fin 7) : ℝ := q i / products x i
def degradation (i : Fin 7) : ℝ := e i / x i

/-- The literal polynomial mass-action vector field, with fixed common rates. -/
def drift (z : Fin 7 → ℝ) : Fin 7 → ℝ :=
  N *ᵥ (fun i => forwardRate i*z i - reverseRate i*products z i) -
    (fun i => degradation i*z i)

def relativeDrift (w : Fin 7 → ℝ) : Fin 7 → ℝ :=
  N *ᵥ ((Matrix.diagonal p) *ᵥ w - (Matrix.diagonal q) *ᵥ products w) -
    (Matrix.diagonal e) *ᵥ w

theorem diag_action (a w : Fin 7 → ℝ) :
    (Matrix.diagonal a) *ᵥ w = fun i => a i*w i := by
  ext i
  exact Matrix.mulVec_diagonal a w i

theorem products_pos (z : Fin 7 → ℝ) (hz : ∀ i, 0 < z i) : ∀ i, 0 < products z i := by
    intro i
    fin_cases i
    · exact mul_pos (hz 1) (hz 5)
    · exact hz 6
    · exact mul_pos (hz 3) (hz 1)
    · exact hz 4
    · exact mul_pos (hz 5) (hz 3)
    · exact hz 0
    · exact hz 2

theorem rates_positive : (∀ i, 0 < forwardRate i) ∧
    (∀ i, 0 < reverseRate i) ∧ (∀ i, 0 < degradation i) := by
  have hx := parameters_positive.2.2.2
  have hp := products_pos x hx
  exact ⟨fun i => div_pos (parameters_positive.2.1 i) (hx i),
    fun i => div_pos (parameters_positive.2.2.1 i) (hp i),
    fun i => div_pos (parameters_positive.1 i) (hx i)⟩

theorem normalize_apply (z : Fin 7 → ℝ) (i : Fin 7) : normalize z i = z i / x i := by
  simp [normalize, Matrix.mulVec_diagonal, div_eq_mul_inv, mul_comm]

theorem normalize_x : normalize x = 1 := by
  ext i
  rw [normalize_apply, div_self (ne_of_gt (parameters_positive.2.2.2 i))]
  rfl

theorem products_normalize (z : Fin 7 → ℝ) :
    products (normalize z) = fun i => products z i / products x i := by
  ext i
  fin_cases i <;> simp [products, normalize_apply, div_mul_div_comm]

theorem drift_eq_relative (z : Fin 7 → ℝ) : drift z = relativeDrift (normalize z) := by
  simp only [drift, relativeDrift, diag_action, products_normalize]
  congr 1
  · congr 1
    ext i
    simp [forwardRate, reverseRate, normalize_apply, div_eq_mul_inv]
    ring
  · ext i
    simp [degradation, normalize_apply, div_eq_mul_inv]
    ring

theorem stationary : drift x = 0 := by
  rw [drift_eq_relative, normalize_x]
  have hp : products (1 : Fin 7 → ℝ) = 1 := by ext i; fin_cases i <;> norm_num [products]
  simp only [relativeDrift, hp, diag_action]
  simpa using sub_eq_zero.mpr stationary_balance

theorem products_derivative : HasFDerivAt products (matrixCLM (1 + N).transpose) (1 : Fin 7 → ℝ) := by
  let pr (j : Fin 7) : (Fin 7 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  let D : (Fin 7 → ℝ) →L[ℝ] (Fin 7 → ℝ) :=
    ContinuousLinearMap.pi ![pr 1+pr 5, pr 6, pr 3+pr 1, pr 4, pr 5+pr 3, pr 0, pr 2]
  have hD : D = matrixCLM (1+N).transpose := by
    ext z i
    fin_cases i <;>
      simp [D, pr, matrixCLM_apply, Matrix.mulVec, dotProduct,
        Matrix.transpose_apply, N, Matrix.one_apply, Fin.sum_univ_succ] <;> ring
  rw [← hD, hasFDerivAt_pi']
  intro i
  have hm (j k : Fin 7) : HasFDerivAt (fun z : Fin 7 → ℝ => z j*z k)
      (pr j + pr k) (1 : Fin 7 → ℝ) := by
    simpa [pr, add_comm] using
      (pr j).hasFDerivAt.mul ((pr k).hasFDerivAt (x := (1 : Fin 7 → ℝ)))
  fin_cases i
  · simpa [products, D] using hm 1 5
  · simpa [products, D, pr] using (pr 6).hasFDerivAt (x := (1 : Fin 7 → ℝ))
  · simpa [products, D] using hm 3 1
  · simpa [products, D, pr] using (pr 4).hasFDerivAt (x := (1 : Fin 7 → ℝ))
  · simpa [products, D] using hm 5 3
  · simpa [products, D, pr] using (pr 0).hasFDerivAt (x := (1 : Fin 7 → ℝ))
  · simpa [products, D, pr] using (pr 2).hasFDerivAt (x := (1 : Fin 7 → ℝ))

theorem relative_derivative : HasFDerivAt relativeDrift (matrixCLM H) (1 : Fin 7 → ℝ) := by
  have hr := (matrixCLM (Matrix.diagonal q)).hasFDerivAt.comp _ products_derivative
  have hf := (matrixCLM (Matrix.diagonal p)).hasFDerivAt (x := (1 : Fin 7 → ℝ))
  have hh := ((matrixCLM N).hasFDerivAt.comp _ (hf.sub hr)).sub
    (matrixCLM (Matrix.diagonal e)).hasFDerivAt
  have hL : matrixCLM H =
      (matrixCLM N).comp (matrixCLM (Matrix.diagonal p) -
        (matrixCLM (Matrix.diagonal q)).comp (matrixCLM (1+N).transpose)) -
      matrixCLM (Matrix.diagonal e) := by
    ext z i
    simp [H, scaledJacobian, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec]
  rw [hL]
  exact hh

theorem physical_derivative : HasFDerivAt drift (matrixCLM A) x := by
  have hr : HasFDerivAt relativeDrift (matrixCLM H) (normalize x) := by
    rw [normalize_x]; exact relative_derivative
  have hh := hr.comp x normalize.hasFDerivAt
  have hfun : drift = relativeDrift ∘ normalize := funext drift_eq_relative
  have hL : matrixCLM A = (matrixCLM H).comp normalize := by
    ext z i
    change (A *ᵥ z) i = (H *ᵥ normalize z) i
    simp only [Matrix.mulVec, dotProduct]
    simp_rw [normalize_apply]
    simp [A, div_eq_mul_inv, mul_comm, mul_left_comm]
  rw [hfun, hL]
  exact hh

end
end TypeIIStability.Witness
