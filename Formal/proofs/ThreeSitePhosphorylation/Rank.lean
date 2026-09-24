import proofs.ThreeSitePhosphorylation.Source

namespace ThreeSitePhosphorylation
noncomputable section
set_option maxHeartbeats 1000000

def tangentMap : (Fin 9 → ℝ) →ₗ[ℝ] State where
  toFun y := ![-y 0-y 3,y 0-y 1-y 4-y 6,y 1-y 2-y 5-y 7,y 2-y 8,
    -y 3-y 4-y 5,-y 6-y 7-y 8,y 3,y 4,y 5,y 6,y 7,y 8]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' c u := by ext i; fin_cases i <;> simp <;> ring

def stoichiometricMap : (Fin 18 → ℝ) →ₗ[ℝ] State where
  toFun := balance
  map_add' u v := by ext i; fin_cases i <;> simp [balance] <;> ring
  map_smul' c u := by ext i; fin_cases i <;> simp [balance] <;> ring

theorem project_tangent (y : Fin 9 → ℝ) : project (tangentMap y) = y := by
  ext i; fin_cases i <;> simp [project,tangentMap] <;> ring

theorem tangent_injective : Function.Injective tangentMap := by
  intro u v h
  have hp := congrArg project h
  simpa only [project_tangent] using hp

def fluxSection (y : Fin 9 → ℝ) : Fin 18 → ℝ :=
  ![y 0+y 3,0,y 0,y 1+y 4,0,y 1,y 2+y 5,0,y 2,y 6,0,0,y 7,0,0,y 8,0,0]

theorem source_covers_tangent (y : Fin 9 → ℝ) :
    stoichiometricMap (fluxSection y) = tangentMap y := by
  ext i; fin_cases i <;> simp [stoichiometricMap,fluxSection,balance,tangentMap] <;> ring

theorem source_is_tangent (v : Fin 18 → ℝ) :
    tangentMap (project (stoichiometricMap v)) = stoichiometricMap v := by
  ext i; fin_cases i <;> simp [tangentMap,project,stoichiometricMap,balance] <;> ring

theorem source_range : LinearMap.range stoichiometricMap = LinearMap.range tangentMap := by
  ext x
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨project (stoichiometricMap v),source_is_tangent v⟩
  · rintro ⟨y,rfl⟩
    exact ⟨fluxSection y,source_covers_tangent y⟩

theorem source_rank_nine : Module.finrank ℝ (LinearMap.range stoichiometricMap) = 9 := by
  rw [source_range,LinearMap.finrank_range_of_inj tangent_injective]
  simp

theorem chart_eq_tangent (y : Fin 9 → ℝ) : chart y = witnessState + tangentMap y := by
  rfl

end
end ThreeSitePhosphorylation
