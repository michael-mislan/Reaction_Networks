import proofs.ThreeSitePhosphorylation.Jacobian

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 300000

theorem jacobianOperator_affine (r : ℝ) :
    jacobianOperator r = jacobianOperator 0 + r • (jacobianOperator 1-jacobianOperator 0) := by
  ext y i
  fin_cases i <;>
    simp [jacobianOperator,jacobianRows,complexLinear,bindingRates,exitRates,
      witnessState,inputSpecies,enzymeSpecies,boundCoordinate,coordinate,speciesVariation]
  ring

theorem jacobianOperator_smooth : ContDiff ℝ ⊤ jacobianOperator := by
  have he : jacobianOperator = (fun r => jacobianOperator 0+r •
      (jacobianOperator 1-jacobianOperator 0)) := funext jacobianOperator_affine
  rw [he]
  fun_prop

theorem quadraticField_smooth :
    ContDiff ℝ ⊤ (fun p : ℝ × ReducedState => quadraticField p.1 p.2) := by
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    simp [quadraticField,complexQuadratic,bindingRates] <;> fun_prop

theorem quadraticField_homogeneous (r a : ℝ) (y : ReducedState) :
    quadraticField r (a • y) = (a*a) • quadraticField r y := by
  ext i
  fin_cases i <;> simp [quadraticField,complexQuadratic] <;> ring

/-- Smooth amplitude-rescaled source, including the zero-amplitude limit. -/
def rescaledField (a r : ℝ) (y : ReducedState) : ReducedState :=
  jacobianOperator r y + a • quadraticField r y

theorem rescaledField_smooth :
    ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × ReducedState => rescaledField p.1.1 p.1.2 p.2) := by
  have hj : ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × ReducedState => jacobianOperator p.1.2) :=
    jacobianOperator_smooth.comp (f := fun p : (ℝ × ℝ) × ReducedState => p.1.2)
      contDiff_fst.snd
  have hq : ContDiff ℝ ⊤ (fun p : (ℝ × ℝ) × ReducedState => quadraticField p.1.2 p.2) :=
    quadraticField_smooth.comp (f := fun p : (ℝ × ℝ) × ReducedState => (p.1.2,p.2))
      (contDiff_fst.snd.prodMk contDiff_snd)
  unfold rescaledField
  apply ContDiff.add
  · exact hj.clm_apply contDiff_snd
  · exact contDiff_fst.fst.smul hq

theorem rescaledField_source (a r : ℝ) (y : ReducedState) :
    a • rescaledField a r y = reducedField r (a • y) := by
  rw [source_taylor_exact,quadraticField_homogeneous]
  simp [rescaledField,smul_add,smul_smul]

theorem rescaledField_zero (r : ℝ) (y : ReducedState) :
    rescaledField 0 r y = jacobianOperator r y := by simp [rescaledField]

theorem rescaledField_zero_derivative (r : ℝ) (y : ReducedState) :
    HasFDerivAt (rescaledField 0 r) (jacobianOperator r) y := by
  have he : rescaledField 0 r = jacobianOperator r := funext (rescaledField_zero r)
  rw [he]
  exact (jacobianOperator r).hasFDerivAt

end
end ThreeSitePhosphorylation
