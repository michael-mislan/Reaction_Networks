import proofs.CoreCouplingGlobal.BasinBoundary

namespace CoreCouplingGlobal
open CoreCouplingCAC

/-- Literal physical Jacobian with p=e*A and stationary B=60/(z+2). -/
noncomputable def stationaryJacobian (e p z : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-2-4*p,z+2*e,60/(z+2),0;
    1+2*p,-1-z-e,-60/(z+2),0;
    1,-z,-60/(z+2)-16-8*z,3;
    0,0,16+4*z,-(20001/10000)]

noncomputable def scaledCharacteristic (e p z l : ℝ) : ℝ :=
  e*(l^3*z+2*l^3+8*l^2*z^2+340001*l^2*z/10000+480001*l^2/5000+
    5001*l*z^2/1250-4998*l*z/625+370023*l/2500+60003/500)+
  l^4*z+2*l^4+9*l^3*z^2+390001*l^3*z/10000+510001*l^3/5000+
  8*l^2*z^3+630009*l^2*z^2/10000+1340037*l^2*z/10000+1600049*l^2/5000+
  15001*l*z^3/1250+540057*l*z^2/10000+120033*l*z/2500+138011*l/500+
  p*(4*l^3*z+8*l^3+34*l^2*z^2+360001*l^2*z/2500+490001*l^2/1250+
    16*l*z^3+580017*l*z^2/5000+220017*l*z/1250+920047*l/1250+
    5001*z^3/625+6*z^2/625-59988*z/625+220023/625)+
  5001*z^3/1250+3*z^2/625-29994*z/625+140031/2500

theorem scaledCharacteristic_eq (e p z l : ℝ) (hz : z+2 ≠ 0) :
    scaledCharacteristic e p z l = (z+2)*(stationaryJacobian e p z).charpoly.eval l := by
  rw [Matrix.eval_charpoly,Matrix.det_succ_row _ 0]
  simp [Matrix.det_fin_three,Fin.sum_univ_succ,stationaryJacobian,
    Matrix.submatrix,Matrix.scalar,Matrix.diagonal,Fin.succAbove]
  field_simp
  unfold scaledCharacteristic
  ring

theorem positive_affine_mix (u a b : ℝ) (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (ha : 0 < a) (hb : 0 < b) : 0 < (1-u)*a+u*b := by
  by_cases h : u = 1
  · simpa only [h,sub_self,zero_mul,one_mul,zero_add] using hb
  · have hleft := mul_pos (by rcases lt_or_eq_of_le hu1 with hh | hh; linarith; exact False.elim (h hh) : 0 < 1-u) ha
    have hright := mul_nonneg hu hb.le
    linarith

theorem positive_cubic_bernstein (t a b c d : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    0 < a*(1-t)^3+3*b*t*(1-t)^2+3*c*t^2*(1-t)+d*t^3 := by
  have h := positive_affine_mix t _ _ ht ht1
    (positive_affine_mix t _ _ ht ht1
      (positive_affine_mix t a b ht ht1 ha hb)
      (positive_affine_mix t b c ht ht1 hb hc))
    (positive_affine_mix t _ _ ht ht1
      (positive_affine_mix t b c ht ht1 hb hc)
      (positive_affine_mix t c d ht ht1 hc hd))
  convert h using 1
  ring

theorem scaledCharacteristic_box_mix (e p z l : ℝ) :
    scaledCharacteristic e p z l =
      (1-50000*e)*((1-(25000/17)*p)*scaledCharacteristic 0 0 z l+
        ((25000/17)*p)*scaledCharacteristic 0 (17/25000) z l)+
      (50000*e)*((1-(25000/17)*p)*scaledCharacteristic (1/50000) 0 z l+
        ((25000/17)*p)*scaledCharacteristic (1/50000) (17/25000) z l) := by
  unfold scaledCharacteristic
  ring

end CoreCouplingGlobal
