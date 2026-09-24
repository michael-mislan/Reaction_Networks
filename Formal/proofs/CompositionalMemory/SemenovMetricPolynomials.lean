import proofs.CompositionalMemory.RationalPolynomialReplay
import proofs.CompositionalMemory.SemenovCountSource

namespace CompositionalMemory.Semenov

def kineticRational (r : Fin 11) : ℚ :=
  if r.val<6 then 13/20 else if r.val=6 then 41/100 else
    if r.val=7 then 463/50000000 else 150

def feedRational (j : Fin 8) : ℚ :=
  if j.val=0 then 1/20 else if j.val=4 then 1/10 else if j.val=7 then 231/100000 else 0

theorem kineticRational_cast (r : Fin 11) : (kineticRational r : ℝ)=nominalRate r := by
  fin_cases r <;> norm_num [kineticRational,nominalRate]

theorem feedRational_cast (j : Fin 8) : (feedRational j : ℝ)=nominalFeed j := by
  fin_cases j <;> norm_num [feedRational,nominalFeed,feed]

def qsub (xs ys : QCoefficients) : QCoefficients := qadd xs (qscale (-1) ys)

@[simp] theorem qpolynomial_qsub (xs ys : QCoefficients) :
    qpolynomial (qsub xs ys)=qpolynomial xs-qpolynomial ys := by
  simp [qsub,sub_eq_add_neg]

theorem qidentity_sound (xs ys : QCoefficients) (h : qzeroCheck (qsub xs ys)=true) :
    qpolynomial xs=qpolynomial ys := by
  have hh := qzeroCheck_sound _ h
  rw [qpolynomial_qsub] at hh
  exact sub_eq_zero.mp hh

def chemicalPolynomial (z : Fin 8 → QCoefficients) (r : Fin 11) : QCoefficients :=
  if r.val=7 then qscale (kineticRational r) (z (reactantA r)) else
    qscale (kineticRational r) (qmul (z (reactantA r)) (z (reactantB r)))

def fieldPolynomial (z : Fin 8 → QCoefficients) (i : Fin 8) : QCoefficients :=
  qadd (qsumFin (fun r : Fin 11 => qscale (stoich r i : ℚ) (chemicalPolynomial z r)))
    (qscale (1/500) (qsub [feedRational i] (z i)))

def chemicalDerivativePolynomial (z : Fin 8 → QCoefficients) (r : Fin 11) (j : Fin 8) : QCoefficients :=
  if r.val=7 then (if j=reactantA r then [kineticRational r] else []) else
    qadd (if j=reactantA r then qscale (kineticRational r) (z (reactantB r)) else [])
      (if j=reactantB r then qscale (kineticRational r) (z (reactantA r)) else [])

def jacobianPolynomial (z : Fin 8 → QCoefficients) (i j : Fin 8) : QCoefficients :=
  qadd (qsumFin (fun r : Fin 11 => qscale (stoich r i : ℚ) (chemicalDerivativePolynomial z r j)))
    [if i=j then -(1/500) else 0]

def forceResidualPolynomial (z : Fin 8 → QCoefficients) (P : Fin 8 → Fin 8 → QCoefficients)
    (timeScale : ℚ) (i : Fin 8) : QCoefficients :=
  qsumFin (fun j => qmul (P i j) (qsub (fieldPolynomial z j) (qscale timeScale (qderivative (z j)))))

def metricResidualPolynomial (z : Fin 8 → QCoefficients) (P : Fin 8 → Fin 8 → QCoefficients)
    (timeScale : ℚ) (i j : Fin 8) : QCoefficients :=
  qadd (qscale timeScale (qderivative (P i j)))
    (qadd (qsumFin (fun l : Fin 8 => qadd (qmul (jacobianPolynomial z l i) (P l j))
      (qmul (P i l) (jacobianPolynomial z l j)))) [if i=j then 1 else 0])

def whitenedPolynomial (P : Fin 8 → Fin 8 → QCoefficients) (A : Fin 8 → Fin 8 → ℚ)
    (i j : Fin 8) : QCoefficients :=
  qsumFin (fun k : Fin 8 => qsumFin (fun l : Fin 8 => qscale (A i k*A j l) (P k l)))

end CompositionalMemory.Semenov
