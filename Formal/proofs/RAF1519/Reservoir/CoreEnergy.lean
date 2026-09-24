import proofs.RAF1519.Reservoir.LowSecantCertificate
import proofs.RAF1519.Reservoir.HighSecantCertificate
import proofs.RAF1519.Reservoir.RootBoxes
import proofs.RAF1519.Reservoir.QuadraticCalculus

namespace RAF1519.Reservoir
noncomputable section
open scoped BigOperators Matrix

def InBox (l u x : Fin 6 → ℝ) : Prop := ∀ i, l i ≤ x i ∧ x i ≤ u i

theorem stationary_energy_decay (P : Matrix (Fin 6) (Fin 6) ℝ) (x c : Fin 6 → ℝ)
    (hc : field c = 0)
    (hu : quadratic P (x-c) ≤ 200*(∑ i, ((x-c) i)^2))
    (hq : (1/2:ℝ)*(∑ i, ((x-c) i)^2) ≤
      quadratic (-(P*secant (features x c)+(secant (features x c)).transpose*P)) (x-c)) :
    quadraticRate P (field x) (x-c) ≤ -(1/400:ℝ)*quadratic P (x-c) := by
  have hf : field x = secant (features x c) *ᵥ (x-c) := by
    funext i
    have h := field_secant x c i
    rw [hc] at h
    simpa only [Pi.zero_apply,sub_zero,Matrix.mulVec,dotProduct,Pi.sub_apply] using h
  rw [hf,quadraticRate_matrix]
  linarith

theorem low_core_coercive (y : Fin 6 → ℝ) :
    (1/1000:ℝ)*(∑ i, (y i)^2) ≤ quadratic lowP y := by
  rw [low_energy_eq,sum_six]
  exact low_coercive y

theorem high_core_coercive (y : Fin 6 → ℝ) :
    (1/1000:ℝ)*(∑ i, (y i)^2) ≤ quadratic highP y := by
  rw [high_energy_eq,sum_six]
  exact high_coercive y

theorem low_core_upper (y : Fin 6 → ℝ) : quadratic lowP y ≤ 200*(∑ i, (y i)^2) := by
  apply quadratic_upper
  intro i
  fin_cases i <;> norm_num [lowP,sum_six]

theorem high_core_upper (y : Fin 6 → ℝ) : quadratic highP y ≤ 200*(∑ i, (y i)^2) := by
  apply quadratic_upper
  intro i
  fin_cases i <;> norm_num [highP,sum_six]

theorem low_feature_lower_eq : lowFeatureLower = featureLower lowBoxLower := by
  funext k
  fin_cases k <;> norm_num [lowFeatureLower,featureLower,lowBoxLower]

theorem low_feature_upper_eq : lowFeatureUpper = featureUpper lowBoxUpper := by
  funext k
  fin_cases k <;> norm_num [lowFeatureUpper,featureUpper,lowBoxUpper]

theorem high_feature_lower_eq : highFeatureLower = featureLower highBoxLower := by
  funext k
  fin_cases k <;> norm_num [highFeatureLower,featureLower,highBoxLower]

theorem high_feature_upper_eq : highFeatureUpper = featureUpper highBoxUpper := by
  funext k
  fin_cases k <;> norm_num [highFeatureUpper,featureUpper,highBoxUpper]

theorem low_core_decay (x c : Fin 6 → ℝ) (hc : field c = 0)
    (hx : InBox lowBoxLower lowBoxUpper x) (hcb : InBox lowBoxLower lowBoxUpper c) :
    quadraticRate lowP (field x) (x-c) ≤ -(1/400:ℝ)*quadratic lowP (x-c) := by
  apply stationary_energy_decay lowP x c hc (low_core_upper (x-c))
  apply low_secant_positive _ _ (by rfl)
  rw [low_feature_lower_eq,low_feature_upper_eq]
  exact features_bounds _ _ x c (fun i => (low_box_positive i).le) hx hcb

theorem high_core_decay (x c : Fin 6 → ℝ) (hc : field c = 0)
    (hx : InBox highBoxLower highBoxUpper x) (hcb : InBox highBoxLower highBoxUpper c) :
    quadraticRate highP (field x) (x-c) ≤ -(1/400:ℝ)*quadratic highP (x-c) := by
  apply stationary_energy_decay highP x c hc (high_core_upper (x-c))
  apply high_secant_positive _ _ (by rfl)
  rw [high_feature_lower_eq,high_feature_upper_eq]
  exact features_bounds _ _ x c (fun i => (high_box_positive i).le) hx hcb

end
end RAF1519.Reservoir
