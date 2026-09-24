import proofs.DynamicSharedResource.Checks
import proofs.DynamicSharedResource.GlobalFlow

namespace DynamicSharedResource.Certificate
noncomputable section
open scoped BigOperators

def reconstruct (a : State) : State := center+basis.mulVec a
def coordinates (u : State) : State := inverse.mulVec (u-center)
def modalField (a : State) : State := inverse.mulVec (nominal (reconstruct a))

theorem coordinates_reconstruct (a : State) : coordinates (reconstruct a)=a := by
  simp only [coordinates,reconstruct,add_sub_cancel_left,Matrix.mulVec_mulVec,
    inverse_basis,Matrix.one_mulVec]

theorem reconstruct_coordinates (u : State) : reconstruct (coordinates u)=u := by
  simp only [coordinates,reconstruct,Matrix.mulVec_mulVec,basis_inverse,Matrix.one_mulVec]
  abel

theorem displacement_bound (q : ℝ) (a : State) (ha : InCube q a) (i : Fin 8) :
    |basis.mulVec a i| ≤ width i*q := by
  rw [← basis_width]
  exact abs_mulVec_le basis a q ha i

theorem displaced_denominator (q : ℝ) (hq : q ≤ 1) (a : State) (ha : InCube q a) :
    0 < 873/10-center 0-basis.mulVec a 0 := by
  have h := displacement_bound q a ha 0
  have hw := width_nonneg 0
  have hd := denominator_margin
  have hb : width 0*q ≤ width 0 := mul_le_of_le_one_right hw hq
  linarith [le_abs_self (basis.mulVec a 0)]

theorem modal_expansion (q : ℝ) (hq : q ≤ 1) (a : State) (ha : InCube q a) :
    modalField a = b + A.mulVec a + C.mulVec (products (basis.mulVec a)) +
      inverse.mulVec (sourceVector (sourceRemainder center (basis.mulVec a))) := by
  have hc : 873/10-center 0 ≠ 0 := by norm_num [center]
  have hd := ne_of_gt (displaced_denominator q hq a ha)
  unfold modalField reconstruct
  rw [nominal_expansion center (basis.mulVec a) hc hd]
  simp only [Matrix.mulVec_add,field_center,inverse_field,Matrix.mulVec_mulVec,
    jac_center,← Matrix.mul_assoc,inverse_jac,left_basis,inverse_reaction]

theorem transformed_source (z : ℝ) (i : Fin 8) :
    inverse.mulVec (sourceVector z) i = inverse i 0*z := by
  simp [Matrix.mulVec,dotProduct,sourceVector,Fin.sum_univ_succ]

theorem modal_remainder (q : ℝ) (hq : (1/2:ℝ) ≤ q) (hq1 : q ≤ 1)
    (a : State) (ha : InCube q a) (i : Fin 8) :
    |modalField a i-b i-A.mulVec a i| ≤ nb i*q^2 := by
  have hq0 : 0 ≤ q := by linarith
  have hp := products_bound (basis.mulVec a) width q width_nonneg hq0
    (displacement_bound q a ha)
  have hs := source_remainder_bound center (basis.mulVec a) width q
    (width_nonneg 0) hq0 hq1 (displacement_bound q a ha 0) denominator_margin
  change |sourceRemainder center (basis.mulVec a)| ≤ sr*q^2 at hs
  have hsum : |C.mulVec (products (basis.mulVec a)) i| ≤
      (∑ j, |C i j| * productBounds width j)*q^2 :=
    sum_products_bound (fun j => C i j) _ _ q hp
  have he := congrFun (modal_expansion q hq1 a ha) i
  simp only [Pi.add_apply,transformed_source] at he
  rw [he]
  have hz : b i+A.mulVec a i+C.mulVec (products (basis.mulVec a)) i+
      inverse i 0*sourceRemainder center (basis.mulVec a)-b i-A.mulVec a i =
      C.mulVec (products (basis.mulVec a)) i+inverse i 0*sourceRemainder center (basis.mulVec a) := by ring
  rw [hz,nb_formula]
  calc
    _ ≤ |C.mulVec (products (basis.mulVec a)) i|+
        |inverse i 0*sourceRemainder center (basis.mulVec a)| := abs_add_le _ _
    _ ≤ (∑ j, |C i j| * productBounds width j)*q^2+|inverse i 0| *(sr*q^2) := by
      rw [abs_mul]
      exact add_le_add hsum (mul_le_mul_of_nonneg_left hs (abs_nonneg _))
    _ = _ := by ring

theorem nominal_face_decay : FaceDecay modalField :=
  faceDecay_of_bounds modalField A b nb nb_nonneg modal_remainder numerical_face_margin

end
end DynamicSharedResource.Certificate
