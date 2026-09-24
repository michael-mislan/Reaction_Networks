import proofs.ThreeSitePhosphorylation.RescaledSource
import proofs.ThreeSitePhosphorylation.Volterra

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 300000

abbrev SourcePath := ContinuousPath ReducedState
abbrev RealPath := ContinuousPath ℝ

def assemblePathLinear : (Fin 9 → RealPath) →ₗ[ℝ] SourcePath where
  toFun u := ⟨fun t i => u i t,continuous_pi (fun i => (u i).continuous)⟩
  map_add' _ _ := by ext t i; rfl
  map_smul' _ _ := by ext t i; rfl

def assemblePath : (Fin 9 → RealPath) →L[ℝ] SourcePath :=
  assemblePathLinear.mkContinuous 1 (by
    intro u
    simp only [one_mul]
    apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
    intro t
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
    intro i
    exact (ContinuousMap.norm_coe_le_norm (u i) t).trans (norm_le_pi_norm u i))

@[simp] theorem assemblePath_apply (u : Fin 9 → RealPath) (t : UnitTime) (i : Fin 9) :
    assemblePath u t i = u i t := rfl

def pathSpecies (j : Fin 12) : SourcePath →L[ℝ] RealPath :=
  (speciesVariation j).compLeftContinuous ℝ UnitTime

@[simp] theorem pathSpecies_apply (j : Fin 12) (u : SourcePath) (t : UnitTime) :
    pathSpecies j u t = speciesVariation j (u t) := rfl

def pathLinear (r : ℝ) : SourcePath →L[ℝ] SourcePath :=
  (jacobianOperator 0).compLeftContinuous ℝ UnitTime + r •
    ((jacobianOperator 1).compLeftContinuous ℝ UnitTime-
      (jacobianOperator 0).compLeftContinuous ℝ UnitTime)

theorem pathLinear_apply (r : ℝ) (u : SourcePath) (t : UnitTime) :
    pathLinear r u t = jacobianOperator r (u t) := by
  rw [jacobianOperator_affine]
  rfl

theorem pathLinear_smooth : ContDiff ℝ ⊤ (fun p : ℝ × SourcePath => pathLinear p.1 p.2) := by
  unfold pathLinear
  fun_prop

def pathComplexQuadratic (r : ℝ) (j : Fin 6) (u : SourcePath) : RealPath :=
  bindingRates r j • (pathSpecies (inputSpecies j) u * pathSpecies (enzymeSpecies j) u)

def pathQuadratic (r : ℝ) (u : SourcePath) : SourcePath :=
  assemblePath ![0,0,0,pathComplexQuadratic r 0 u,pathComplexQuadratic r 1 u,
    pathComplexQuadratic r 2 u,pathComplexQuadratic r 3 u,pathComplexQuadratic r 4 u,
    pathComplexQuadratic r 5 u]

theorem pathQuadratic_apply (r : ℝ) (u : SourcePath) (t : UnitTime) :
    pathQuadratic r u t = quadraticField r (u t) := by
  ext i
  fin_cases i <;> simp [pathQuadratic,pathComplexQuadratic,quadraticField,
    complexQuadratic,mul_assoc]

theorem pathQuadratic_smooth :
    ContDiff ℝ ⊤ (fun p : ℝ × SourcePath => pathQuadratic p.1 p.2) := by
  unfold pathQuadratic
  apply assemblePath.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;> simp [pathComplexQuadratic,bindingRates] <;> fun_prop

def pathField (p : ℝ × (ℝ × ℝ)) (u : SourcePath) : SourcePath :=
  p.2.2 • (pathLinear p.2.1 u+p.1 • pathQuadratic p.2.1 u)

theorem pathField_apply (a r T : ℝ) (u : SourcePath) (t : UnitTime) :
    pathField (a,(r,T)) u t = T • rescaledField a r (u t) := by
  simp [pathField,pathLinear_apply,pathQuadratic_apply,rescaledField]

theorem pathField_smooth :
    ContDiff ℝ ⊤ (fun p : (ℝ × (ℝ × ℝ)) × SourcePath => pathField p.1 p.2) := by
  have hl : ContDiff ℝ ⊤ (fun p : (ℝ × (ℝ × ℝ)) × SourcePath => pathLinear p.1.2.1 p.2) :=
    pathLinear_smooth.comp (f := fun p : (ℝ × (ℝ × ℝ)) × SourcePath => (p.1.2.1,p.2))
      (contDiff_fst.snd.fst.prodMk contDiff_snd)
  have hq : ContDiff ℝ ⊤ (fun p : (ℝ × (ℝ × ℝ)) × SourcePath => pathQuadratic p.1.2.1 p.2) :=
    pathQuadratic_smooth.comp (f := fun p : (ℝ × (ℝ × ℝ)) × SourcePath => (p.1.2.1,p.2))
      (contDiff_fst.snd.fst.prodMk contDiff_snd)
  unfold pathField
  have ht : ContDiff ℝ ⊤ (fun p : (ℝ × (ℝ × ℝ)) × SourcePath => p.1.2.2) := by fun_prop
  have ha : ContDiff ℝ ⊤ (fun p : (ℝ × (ℝ × ℝ)) × SourcePath => p.1.1) := by fun_prop
  exact ht.smul (hl.add (ha.smul hq))

theorem linearPicard_pathLinear (r T : ℝ) (u : SourcePath) :
    linearPicard (ContinuousLinearMap.id ℝ ReducedState) (T • pathLinear r u) =
      linearPicard (T • jacobianOperator r) u := by
  ext t i
  change (∫ s in (0:ℝ)..(t:ℝ), pathExtension (T • pathLinear r u) s) i =
    (∫ s in (0:ℝ)..(t:ℝ), (T • jacobianOperator r) (pathExtension u s)) i
  apply congrArg (fun v : ReducedState => v i)
  apply intervalIntegral.integral_congr
  intro s _
  simp [pathExtension,pathLinear_apply]

end
end ThreeSitePhosphorylation
