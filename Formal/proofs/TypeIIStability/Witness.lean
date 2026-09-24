import proofs.MixedDegradation.StationaryJacobian
import proofs.DUnstableCores.DScaling

namespace TypeIIStability.Witness
noncomputable section
open scoped Matrix BigOperators
set_option maxRecDepth 12000
set_option maxHeartbeats 1600000

def N : Matrix (Fin 7) (Fin 7) ℝ := ![![-1, 0, 0, 0, 0, 1, 0], ![1, -1, 1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 1], ![0, 0, 1, -1, 1, 0, 0], ![0, 0, 0, 1, -1, 0, 0], ![1, 0, 0, 0, 1, -1, 0], ![0, 1, 0, 0, 0, 0, -1]]

def e : Fin 7 → ℝ := ![119498114558151195430200, 50529476583056335199400, 102854639051720636741122800, 50529476583056335199400, 212440931970968885258100, 50529476583056335199400, 50529476583056335199400]

def p : Fin 7 → ℝ := ![104062122335493429347978400, 106240288027945864750558380, 590159088761351472748874775, 432997999695232751087100, 430137041288507329360119900, 103125725596027956942151200, 104373404827035251379435600]

def q : Fin 7 → ℝ := ![1106424330606679936456800, 3072149091088146453778680, 589896118352797447528417275, 50529476583056335199400, 429967013697366121829490300, 50529476583056335199400, 1255795366760589417855300]

def x : Fin 7 → ℝ := ![353827128708175750212000, 166846502377565969557740, 33548594408689902229104300, 701061232230997648855000, 36804829974094783842403500, 50529476583056335199400, 17556019227313040061617094]

def u : Fin 7 → ℝ := ![213, 235, 35, -204, -3, 203, 200]

def v : Fin 7 → ℝ := ![303, 265, -51, -312, -3, 307, 0]

def H : Matrix (Fin 7) (Fin 7) ℝ :=
  MixedDegradation.scaledJacobian N (1 + N) p q e

def A : Matrix (Fin 7) (Fin 7) ℝ := fun i j => H i j / x j

theorem parameters_positive : (∀ i, 0 < e i) ∧ (∀ i, 0 < p i) ∧
    (∀ i, 0 < q i) ∧ (∀ i, 0 < x i) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro i <;> fin_cases i <;> norm_num [e, p, q, x]

theorem stationary_balance : N *ᵥ (p-q) = e := by
  ext i
  fin_cases i <;> norm_num [N, p, q, e, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

theorem pencil_real : H *ᵥ u = fun i => x i * (u i - 8 * v i) := by
  ext i
  fin_cases i <;>
    norm_num [H, MixedDegradation.scaledJacobian, N, p, q, e, x, u, v,
      Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.diagonal, Matrix.one_apply, Fin.sum_univ_succ] <;>
    norm_num [Fin.ext_iff, Fin.succ]

theorem pencil_imag : H *ᵥ v = fun i => x i * (8 * u i + v i) := by
  ext i
  fin_cases i <;>
    norm_num [H, MixedDegradation.scaledJacobian, N, p, q, e, x, u, v,
      Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.diagonal, Matrix.one_apply, Fin.sum_univ_succ] <;>
    norm_num [Fin.ext_iff, Fin.succ]

end
end TypeIIStability.Witness
