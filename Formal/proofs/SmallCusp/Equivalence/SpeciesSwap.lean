import proofs.SmallCusp.Normalization.FluxJet

/-!
# Cusp transport under exchange of the two species

Species exchange is a coordinate permutation.  The identities below expose
that mechanism once, rather than duplicating every finite source certificate.
-/

open scoped BigOperators

namespace SmallCusp

def swapSpeciesVector {R : Type} (v : Species → R) : Species → R :=
  fun i ↦ v (Fin.rev i)

@[simp] theorem swapComplex_swap (y : Complex) :
    swapComplex (swapComplex y) = y := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem swapSpeciesVector_swap {R : Type} (v : Species → R) :
    swapSpeciesVector (swapSpeciesVector v) = v := by
  funext i
  fin_cases i <;> rfl

def swapSpeciesNetwork {m : ℕ} (Q : SmallPlanarNetwork m) :
    SmallPlanarNetwork m where
  reactant r := swapComplex (Q.reactant r)
  product r := swapComplex (Q.product r)
  noSelfReaction := by
    intro r h
    apply Q.noSelfReaction r
    simpa using congrArg swapComplex h
  reactionInjective := by
    intro r s h
    apply Q.reactionInjective
    apply Prod.ext
    · simpa using congrArg (fun z ↦ swapComplex z) (congrArg Prod.fst h)
    · simpa using congrArg (fun z ↦ swapComplex z) (congrArg Prod.snd h)

@[simp] theorem swapSpeciesNetwork_stoich {m : ℕ}
    (Q : SmallPlanarNetwork m) (i : Species) (r : Fin m) :
    (swapSpeciesNetwork Q).stoich i r = Q.stoich (Fin.rev i) r := by
  fin_cases i <;> rfl

theorem swapSpeciesNetwork_monomial {m : ℕ}
    (Q : SmallPlanarNetwork m) (r : Fin m) (x : Species → ℝ) :
    (swapSpeciesNetwork Q).monomial r (swapSpeciesVector x) = Q.monomial r x := by
  simp [SmallPlanarNetwork.monomial, swapSpeciesNetwork, swapSpeciesVector,
    swapComplex, Fin.prod_univ_two]
  ring

theorem swapSpeciesNetwork_multiDerivative {m : ℕ}
    (Q : SmallPlanarNetwork m) (r : Fin m) (d : Species → ℕ)
    (x : Species → ℝ) :
    (swapSpeciesNetwork Q).multiDerivativeMonomial r
        (swapSpeciesVector d) (swapSpeciesVector x) =
      Q.multiDerivativeMonomial r d x := by
  simp [SmallPlanarNetwork.multiDerivativeMonomial, swapSpeciesNetwork,
    swapSpeciesVector, swapComplex, Fin.prod_univ_two]
  ring

@[simp] theorem swapSpeciesVector_unitMultiIndex (j : Species) :
    swapSpeciesVector (SmallPlanarNetwork.unitMultiIndex j) =
      SmallPlanarNetwork.unitMultiIndex (Fin.rev j) := by
  funext i
  fin_cases i <;> fin_cases j <;>
    simp [swapSpeciesVector, SmallPlanarNetwork.unitMultiIndex]

@[simp] theorem swapSpeciesVector_pairMultiIndex (j l : Species) :
    swapSpeciesVector (SmallPlanarNetwork.pairMultiIndex j l) =
      SmallPlanarNetwork.pairMultiIndex (Fin.rev j) (Fin.rev l) := by
  funext i
  fin_cases i <;> fin_cases j <;> fin_cases l <;>
    simp [swapSpeciesVector, SmallPlanarNetwork.pairMultiIndex]

theorem swapSpeciesNetwork_massAction {m : ℕ}
    (Q : SmallPlanarNetwork m) (k : Fin m → ℝ) (x : Species → ℝ)
    (i : Species) :
    (swapSpeciesNetwork Q).massAction k (swapSpeciesVector x) i =
      Q.massAction k x (Fin.rev i) := by
  unfold SmallPlanarNetwork.massAction
  apply Finset.sum_congr rfl
  intro r _
  rw [swapSpeciesNetwork_stoich, swapSpeciesNetwork_monomial]

theorem swapSpeciesNetwork_jacobian {m : ℕ}
    (Q : SmallPlanarNetwork m) (k : Fin m → ℝ) (x : Species → ℝ)
    (i j : Species) :
    (swapSpeciesNetwork Q).jacobian k (swapSpeciesVector x) i j =
      Q.jacobian k x (Fin.rev i) (Fin.rev j) := by
  unfold SmallPlanarNetwork.jacobian
  apply Finset.sum_congr rfl
  intro r _
  rw [swapSpeciesNetwork_stoich]
  have hm := swapSpeciesNetwork_multiDerivative Q r
    (SmallPlanarNetwork.unitMultiIndex (Fin.rev j)) x
  simpa using congrArg (fun z ↦ (Q.stoich (Fin.rev i) r : ℝ) * k r * z) hm

theorem swapSpeciesNetwork_hessian {m : ℕ}
    (Q : SmallPlanarNetwork m) (k : Fin m → ℝ) (x : Species → ℝ)
    (i j l : Species) :
    (swapSpeciesNetwork Q).hessian k (swapSpeciesVector x) i j l =
      Q.hessian k x (Fin.rev i) (Fin.rev j) (Fin.rev l) := by
  unfold SmallPlanarNetwork.hessian
  apply Finset.sum_congr rfl
  intro r _
  rw [swapSpeciesNetwork_stoich]
  have hm := swapSpeciesNetwork_multiDerivative Q r
    (SmallPlanarNetwork.pairMultiIndex (Fin.rev j) (Fin.rev l)) x
  simpa using congrArg (fun z ↦ (Q.stoich (Fin.rev i) r : ℝ) * k r * z) hm

theorem dot_swapSpeciesVector (u v : Species → ℝ) :
    dot (swapSpeciesVector u) (swapSpeciesVector v) = dot u v := by
  simp [dot, swapSpeciesVector, Fin.sum_univ_two, add_comm]

theorem swapSpeciesNetwork_jacobianApply {m : ℕ}
    (Q : SmallPlanarNetwork m) (k : Fin m → ℝ)
    (x v : Species → ℝ) (i : Species) :
    (swapSpeciesNetwork Q).jacobianApply k (swapSpeciesVector x)
        (swapSpeciesVector v) i =
      Q.jacobianApply k x v (Fin.rev i) := by
  fin_cases i <;>
    simp [SmallPlanarNetwork.jacobianApply, Fin.sum_univ_two,
      swapSpeciesVector, swapSpeciesNetwork_jacobian, add_comm]

theorem swapSpeciesNetwork_hessianApply {m : ℕ}
    (Q : SmallPlanarNetwork m) (k : Fin m → ℝ)
    (x u v : Species → ℝ) (i : Species) :
    (swapSpeciesNetwork Q).hessianApply k (swapSpeciesVector x)
        (swapSpeciesVector u) (swapSpeciesVector v) i =
      Q.hessianApply k x u v (Fin.rev i) := by
  fin_cases i <;>
    simp [SmallPlanarNetwork.hessianApply, Fin.sum_univ_two,
      swapSpeciesVector, swapSpeciesNetwork_hessian, add_comm]

theorem swapSpeciesNetwork_rateFieldVariation {m : ℕ}
    (Q : SmallPlanarNetwork m) (u : Fin m → ℝ) (x : Species → ℝ)
    (i : Species) :
    (swapSpeciesNetwork Q).rateFieldVariation u (swapSpeciesVector x) i =
      Q.rateFieldVariation u x (Fin.rev i) := by
  unfold SmallPlanarNetwork.rateFieldVariation
  apply Finset.sum_congr rfl
  intro r _
  rw [swapSpeciesNetwork_stoich, swapSpeciesNetwork_monomial]

theorem swapSpeciesNetwork_rateJacobianVariation {m : ℕ}
    (Q : SmallPlanarNetwork m) (u : Fin m → ℝ)
    (x q : Species → ℝ) (i : Species) :
    (swapSpeciesNetwork Q).rateJacobianVariation u (swapSpeciesVector x)
        (swapSpeciesVector q) i =
      Q.rateJacobianVariation u x q (Fin.rev i) := by
  unfold SmallPlanarNetwork.rateJacobianVariation
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_bij (fun j _ ↦ Fin.rev j)
  · intro j hj
    simp only [Finset.mem_univ]
  · intro a ha b hb hab
    simpa using congrArg Fin.rev hab
  · intro j hj
    exact ⟨Fin.rev j, Finset.mem_univ _, by simp⟩
  · intro j _
    rw [swapSpeciesNetwork_stoich]
    have hm := swapSpeciesNetwork_multiDerivative Q r
      (SmallPlanarNetwork.unitMultiIndex (Fin.rev j)) x
    have hm' : (swapSpeciesNetwork Q).multiDerivativeMonomial r
        (SmallPlanarNetwork.unitMultiIndex j) (swapSpeciesVector x) =
        Q.multiDerivativeMonomial r
          (SmallPlanarNetwork.unitMultiIndex (Fin.rev j)) x := by
      simpa only [swapSpeciesVector_unitMultiIndex, Fin.rev_rev] using hm
    rw [hm']
    rfl

def swapSpeciesCertificate {m : ℕ} {Q : SmallPlanarNetwork m}
    (C : CuspCertificate Q) : CuspCertificate (swapSpeciesNetwork Q) where
  state := swapSpeciesVector C.state
  rates := C.rates
  rightKernel := swapSpeciesVector C.rightKernel
  leftKernel := swapSpeciesVector C.leftKernel
  centerCorrection := swapSpeciesVector C.centerCorrection
  unfoldingDirections := C.unfoldingDirections

theorem swapSpeciesCertificate_valid {m : ℕ} {Q : SmallPlanarNetwork m}
    (C : CuspCertificate Q) (hC : C.Valid) :
    (swapSpeciesCertificate C).Valid := by
  rcases hC with ⟨hx, hk, heq, hright, hleft, hnorm, htrace,
    hfold, hcenter, hcenterNorm, hcubic, hunfold⟩
  refine ⟨?_, hk, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hx (Fin.rev i)
  · intro i
    simpa [swapSpeciesCertificate] using
      swapSpeciesNetwork_massAction Q C.rates C.state i
        |>.trans (heq (Fin.rev i))
  · intro i
    simpa [swapSpeciesCertificate] using
      swapSpeciesNetwork_jacobianApply Q C.rates C.state C.rightKernel i
        |>.trans (hright (Fin.rev i))
  · intro j
    fin_cases j
    · simpa [swapSpeciesCertificate, swapSpeciesVector, Fin.sum_univ_two,
        swapSpeciesNetwork_jacobian, add_comm] using hleft 1
    · simpa [swapSpeciesCertificate, swapSpeciesVector, Fin.sum_univ_two,
        swapSpeciesNetwork_jacobian, add_comm] using hleft 0
  · simpa [swapSpeciesCertificate] using
      dot_swapSpeciesVector C.leftKernel C.rightKernel |>.trans hnorm
  · simpa [swapSpeciesCertificate, swapSpeciesNetwork_jacobian, add_comm] using htrace
  · have hv : (swapSpeciesNetwork Q).hessianApply C.rates
        (swapSpeciesVector C.state) (swapSpeciesVector C.rightKernel)
        (swapSpeciesVector C.rightKernel) =
        swapSpeciesVector
          (Q.hessianApply C.rates C.state C.rightKernel C.rightKernel) := by
      funext i
      exact swapSpeciesNetwork_hessianApply Q C.rates C.state
        C.rightKernel C.rightKernel i
    simpa [swapSpeciesCertificate, hv] using
      dot_swapSpeciesVector C.leftKernel
        (Q.hessianApply C.rates C.state C.rightKernel C.rightKernel) |>.trans hfold
  · intro i
    change (swapSpeciesNetwork Q).jacobianApply C.rates
        (swapSpeciesVector C.state) (swapSpeciesVector C.centerCorrection) i =
      -(swapSpeciesNetwork Q).hessianApply C.rates
        (swapSpeciesVector C.state) (swapSpeciesVector C.rightKernel)
          (swapSpeciesVector C.rightKernel) i
    rw [swapSpeciesNetwork_jacobianApply, swapSpeciesNetwork_hessianApply]
    exact hcenter (Fin.rev i)
  · simpa [swapSpeciesCertificate] using
      dot_swapSpeciesVector C.leftKernel C.centerCorrection |>.trans hcenterNorm
  · have hv : (swapSpeciesNetwork Q).hessianApply C.rates
        (swapSpeciesVector C.state) (swapSpeciesVector C.rightKernel)
        (swapSpeciesVector C.centerCorrection) =
        swapSpeciesVector
          (Q.hessianApply C.rates C.state C.rightKernel C.centerCorrection) := by
      funext i
      exact swapSpeciesNetwork_hessianApply Q C.rates C.state
        C.rightKernel C.centerCorrection i
    simpa [swapSpeciesCertificate, hv] using
      (show dot (swapSpeciesVector C.leftKernel)
          (swapSpeciesVector (Q.hessianApply C.rates C.state
            C.rightKernel C.centerCorrection)) ≠ 0 from by
        simpa [dot_swapSpeciesVector] using hcubic)
  · have hMatrix : (swapSpeciesCertificate C).unfoldingMatrix =
        C.unfoldingMatrix := by
      ext row col
      by_cases hr : row = 0
      · subst row
        simp only [CuspCertificate.unfoldingMatrix,
          CuspCertificate.unfoldingEntry, if_pos, swapSpeciesCertificate]
        have hv : (swapSpeciesNetwork Q).rateFieldVariation
            (C.unfoldingDirections col) (swapSpeciesVector C.state) =
            swapSpeciesVector
              (Q.rateFieldVariation (C.unfoldingDirections col) C.state) := by
          funext i
          exact swapSpeciesNetwork_rateFieldVariation Q
            (C.unfoldingDirections col) C.state i
        rw [hv, dot_swapSpeciesVector]
      · simp only [CuspCertificate.unfoldingMatrix,
          CuspCertificate.unfoldingEntry, hr, if_false, swapSpeciesCertificate]
        have hv : (swapSpeciesNetwork Q).rateJacobianVariation
            (C.unfoldingDirections col) (swapSpeciesVector C.state)
              (swapSpeciesVector C.rightKernel) =
            swapSpeciesVector
              (Q.rateJacobianVariation (C.unfoldingDirections col)
                C.state C.rightKernel) := by
          funext i
          exact swapSpeciesNetwork_rateJacobianVariation Q
            (C.unfoldingDirections col) C.state C.rightKernel i
        rw [hv, dot_swapSpeciesVector]
    rw [hMatrix]
    exact hunfold

theorem swapSpecies_admitsTransverseCusp_iff {m : ℕ}
    (Q : SmallPlanarNetwork m) :
    AdmitsTransverseCusp (swapSpeciesNetwork Q) ↔ AdmitsTransverseCusp Q := by
  constructor
  · rintro ⟨C, hC⟩
    have h := swapSpeciesCertificate_valid C hC
    simpa [swapSpeciesNetwork, swapSpeciesCertificate] using
      (show AdmitsTransverseCusp (swapSpeciesNetwork (swapSpeciesNetwork Q)) from ⟨_, h⟩)
  · rintro ⟨C, hC⟩
    exact ⟨swapSpeciesCertificate C, swapSpeciesCertificate_valid C hC⟩

end SmallCusp
