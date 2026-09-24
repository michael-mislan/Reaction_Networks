import proofs.SmallCusp.Obstruction.ConicDeterminant

/-!
# Computed five-reaction conic certificates

`upperConicCoeff` computes the polynomial left after subtracting equilibrium
row multiples from a signed Jacobian determinant.  The generic identity below
means finite instances need verify only coefficient nonnegativity and one
strictly positive entry.
-/

namespace SmallCusp

def unitJacobianEntryCoeff (Q : SmallPlanarNetwork 5)
    (i j : Species) (r : Fin 5) : ℝ :=
  (Q.stoich i r : ℝ) * Q.reactant r j

def orderedUnitDetCoeff (Q : SmallPlanarNetwork 5) (r s : Fin 5) : ℝ :=
  unitJacobianEntryCoeff Q 0 0 r * unitJacobianEntryCoeff Q 1 1 s -
    unitJacobianEntryCoeff Q 0 1 r * unitJacobianEntryCoeff Q 1 0 s

def rawConicCoeff (Q : SmallPlanarNetwork 5) (sign : ℝ)
    (multiplier : Species → Fin 5 → ℝ) (r s : Fin 5) : ℝ :=
  sign * orderedUnitDetCoeff Q r s -
    ∑ i : Species, multiplier i r * (Q.stoich i s : ℝ)

def upperConicCoeff (Q : SmallPlanarNetwork 5) (sign : ℝ)
    (multiplier : Species → Fin 5 → ℝ) (r s : Fin 5) : ℝ :=
  if r < s then rawConicCoeff Q sign multiplier r s +
      rawConicCoeff Q sign multiplier s r
  else if r = s then rawConicCoeff Q sign multiplier r r
  else 0

theorem upperConicCoeff_identity (Q : SmallPlanarNetwork 5) (sign : ℝ)
    (multiplier : Species → Fin 5 → ℝ) (v : Fin 5 → ℝ) :
    sign * unitJacobianDet Q v =
      (∑ r : Fin 5, ∑ s : Fin 5,
        upperConicCoeff Q sign multiplier r s * v r * v s) +
      ∑ i : Species,
        (∑ r : Fin 5, multiplier i r * v r) *
          Q.massAction v unitState i := by
  simp [unitJacobianDet, upperConicCoeff, rawConicCoeff,
    orderedUnitDetCoeff, unitJacobianEntryCoeff,
    SmallPlanarNetwork.jacobian, SmallPlanarNetwork.massAction,
    SmallPlanarNetwork.multiDerivativeMonomial,
    SmallPlanarNetwork.monomial, SmallPlanarNetwork.unitMultiIndex,
    unitState, Fin.sum_univ_succ, Fin.prod_univ_two]
  ring

theorem upperConicCertificate_excludes_cusp (Q : SmallPlanarNetwork 5)
    (sign : ℝ) (multiplier : Species → Fin 5 → ℝ)
    (hc : ∀ r s, 0 ≤ upperConicCoeff Q sign multiplier r s)
    (hw : ∃ r s, 0 < upperConicCoeff Q sign multiplier r s) :
    ¬ AdmitsTransverseCusp Q := by
  apply conicDeterminantCertificate_excludes_cusp Q sign
    (upperConicCoeff Q sign multiplier) multiplier hc hw
  exact upperConicCoeff_identity Q sign multiplier

end SmallCusp
