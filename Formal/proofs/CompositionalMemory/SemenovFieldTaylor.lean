import proofs.CompositionalMemory.SemenovMetricPolynomials

namespace CompositionalMemory.Semenov
open Polynomial

noncomputable def chemicalValue (z : Fin 8 → ℝ) (r : Fin 11) : ℝ :=
  if r.val=7 then nominalRate r*z (reactantA r) else
    nominalRate r*z (reactantA r)*z (reactantB r)

noncomputable def chemicalLinear (z h : Fin 8 → ℝ) (r : Fin 11) : ℝ :=
  if r.val=7 then nominalRate r*h (reactantA r) else
    nominalRate r*(h (reactantA r)*z (reactantB r)+z (reactantA r)*h (reactantB r))

noncomputable def chemicalQuadratic (h : Fin 8 → ℝ) (r : Fin 11) : ℝ :=
  if r.val=7 then 0 else nominalRate r*h (reactantA r)*h (reactantB r)

noncomputable def fieldValue (z : Fin 8 → ℝ) (i : Fin 8) : ℝ :=
  (∑ r,(stoich r i : ℝ)*chemicalValue z r)+(1/500)*(nominalFeed i-z i)

noncomputable def fieldLinear (z h : Fin 8 → ℝ) (i : Fin 8) : ℝ :=
  (∑ r,(stoich r i : ℝ)*chemicalLinear z h r)-(1/500)*h i

noncomputable def chemicalDerivativeValue (z : Fin 8 → ℝ) (r : Fin 11) (j : Fin 8) : ℝ :=
  if r.val=7 then (if j=reactantA r then nominalRate r else 0) else
    (if j=reactantA r then nominalRate r*z (reactantB r) else 0)+
    (if j=reactantB r then nominalRate r*z (reactantA r) else 0)

noncomputable def jacobianValue (z : Fin 8 → ℝ) (i j : Fin 8) : ℝ :=
  (∑ r,(stoich r i : ℝ)*chemicalDerivativeValue z r j)+
    if i=j then -(1/500) else 0

theorem chemicalLinear_eq_sum (z h : Fin 8 → ℝ) (r : Fin 11) :
    chemicalLinear z h r=∑ j,chemicalDerivativeValue z r j*h j := by
  by_cases hr : r.val=7
  · simp [chemicalLinear,chemicalDerivativeValue,hr,ite_mul]
  · simp only [chemicalLinear,chemicalDerivativeValue,if_neg hr,add_mul,ite_mul,zero_mul,Finset.sum_add_distrib]
    simp
    ring

theorem jacobian_action (z h : Fin 8 → ℝ) (i : Fin 8) :
    (∑ j,jacobianValue z i j*h j)=fieldLinear z h i := by
  simp only [jacobianValue,add_mul,Finset.sum_add_distrib,Finset.sum_mul,mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum,← chemicalLinear_eq_sum]
  have hf : (∑ j,(if i=j then -(1/500 : ℝ) else 0)*h j)=-(1/500 : ℝ)*h i := by
    simp [ite_mul]
  rw [hf]
  unfold fieldLinear
  ring

theorem chemical_taylor_exact (z h : Fin 8 → ℝ) (r : Fin 11) :
    chemicalValue (fun j => z j+h j) r=chemicalValue z r+chemicalLinear z h r+chemicalQuadratic h r := by
  by_cases hr : r.val=7 <;> simp only [chemicalValue,chemicalLinear,chemicalQuadratic,hr,ite_true,ite_false] <;> ring

theorem field_taylor_exact (z h : Fin 8 → ℝ) (i : Fin 8) :
    fieldValue (fun j => z j+h j) i=fieldValue z i+fieldLinear z h i+
      ∑ r,(stoich r i : ℝ)*chemicalQuadratic h r := by
  simp only [fieldValue,fieldLinear,chemical_taylor_exact,mul_add,Finset.sum_add_distrib]
  ring

theorem chemical_polynomial_value (z : Fin 8 → QCoefficients) (r : Fin 11) (t : ℝ) :
    aeval t (qpolynomial (chemicalPolynomial z r))=
      chemicalValue (fun j => aeval t (qpolynomial (z j))) r := by
  by_cases hr : r.val=7
  · simp only [chemicalPolynomial,chemicalValue,if_pos hr,qpolynomial_qscale,map_mul,aeval_C]
    change (kineticRational r : ℝ)*_=nominalRate r*_
    rw [kineticRational_cast]
  · simp only [chemicalPolynomial,chemicalValue,if_neg hr,qpolynomial_qscale,qpolynomial_qmul,map_mul,aeval_C]
    change (kineticRational r : ℝ)*(_*_)=nominalRate r*_*_
    rw [kineticRational_cast]
    ring

theorem field_polynomial_value (z : Fin 8 → QCoefficients) (i : Fin 8) (t : ℝ) :
    aeval t (qpolynomial (fieldPolynomial z i))=
      fieldValue (fun j => aeval t (qpolynomial (z j))) i := by
  simp only [fieldPolynomial,qpolynomial_qadd,qpolynomial_qsumFin,qpolynomial_qscale,qpolynomial_qsub,
    map_add,map_sum,map_mul,aeval_C,map_sub,chemical_polynomial_value]
  norm_num only [map_intCast,map_div₀,map_ofNat,map_one]
  change (∑ r,(stoich r i : ℝ)*chemicalValue (fun j => aeval t (qpolynomial (z j))) r)+
    (1/500 : ℝ)*(aeval t (qpolynomial [feedRational i])-aeval t (qpolynomial (z i)))=_
  simp only [qpolynomial,aeval_C,mul_zero,add_zero]
  change _+(1/500 : ℝ)*((feedRational i : ℝ)-_)=_
  rw [feedRational_cast]
  rfl

theorem bimolecular_reactants_distinct (r : Fin 11) (hr : r.val ≠ 7) : reactantA r ≠ reactantB r := by
  exact (by decide : ∀ r : Fin 11,r.val ≠ 7 → reactantA r ≠ reactantB r) r hr

end CompositionalMemory.Semenov
