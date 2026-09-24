import proofs.CoreCouplingGlobal.ResponseLinearization

namespace CoreCouplingGlobal
open Set

def saddlePairing (g v : SaddleVector) : ℝ := ∑ i, g i*v i

theorem saddlePairing_add_right (g v w : SaddleVector) :
    saddlePairing g (v+w) = saddlePairing g v+saddlePairing g w := by
  simp [saddlePairing,mul_add,Finset.sum_add_distrib]

theorem saddlePairing_abs_bound (g v : SaddleVector) :
    |saddlePairing g v| ≤ 4*‖g‖*‖v‖ := by
  calc
    |saddlePairing g v| ≤ ∑ i : Fin 4, |g i*v i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 4, ‖g‖*‖v‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      rw [abs_mul]
      exact mul_le_mul (norm_le_pi_norm g i) (norm_le_pi_norm v i)
        (abs_nonneg _) (norm_nonneg _)
    _ = 4*‖g‖*‖v‖ := by simp; ring

noncomputable def saddleGradient (e z : ℝ) : SaddleVector →ₗ[ℝ] SaddleVector where
  toFun x :=
    let B := 60/(z+2)
    let m := localForkSlope e B z
    let w := localWeight z
    let n := localHSlope z
    ![m*(2+z)*x 0+m*B*x 1,
      m*B*x 0+(B+16+8*z)*x 1/w-3*x 2/w,
      -3*x 1/w+n*(20001/10000)*x 2,x 3]
  map_add' x y := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' a x := by
    ext i
    fin_cases i <;> simp <;> ring

theorem saddleGradient_linear_rate (e z a : ℝ) (x : SaddleVector) :
    saddlePairing (saddleGradient e z x)
      (responseCoordinateLinear (60/(z+2)) z (responseSlope e (60/(z+2))) a x) =
        saddleQuadraticRate e z a x := by
  simp [saddlePairing,Fin.sum_univ_succ,saddleGradient,responseCoordinateLinear,
    saddleQuadraticRate]
  ring

/-- Strict linear dissipation survives a sufficiently small two-point remainder. -/
theorem strict_linear_dissipation_persists (f : SaddleVector → SaddleVector)
    (G L : SaddleVector →L[ℝ] SaddleVector) (p : SaddleVector)
    (hd : HasStrictFDerivAt f L p) (κ : ℝ) (hκ : 0 < κ)
    (hlinear : ∀ v, saddlePairing (G v) (L v) ≤ -(κ*‖v‖^2)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : SaddleVector, dist x p < δ → dist y p < δ →
      saddlePairing (G (x-y)) (f x-f y) ≤ -((κ/2)*‖x-y‖^2) := by
  obtain ⟨C,hC,hG⟩ := G.bound
  have hε : 0 < κ/(8*C) := by positivity
  obtain ⟨δ,hδ,hrem⟩ := strict_derivative_two_point_bound f L p hd (κ/(8*C)) hε
  refine ⟨δ,hδ,?_⟩
  intro x y hx hy
  let v := x-y
  let R := f x-f y-L v
  have hR : ‖R‖ ≤ κ/(8*C)*‖v‖ := hrem x y hx hy
  have hprod := mul_le_mul (hG v) hR (norm_nonneg R) (by positivity : 0 ≤ C*‖v‖)
  have herr := saddlePairing_abs_bound (G v) R
  have hscale : 4*(C*‖v‖)*(κ/(8*C)*‖v‖) = (κ/2)*‖v‖^2 := by
    field_simp
    ring
  have herr' : saddlePairing (G v) R ≤ (κ/2)*‖v‖^2 := by
    have h := mul_le_mul_of_nonneg_left hprod (by norm_num : (0:ℝ) ≤ 4)
    have habs := le_abs_self (saddlePairing (G v) R)
    nlinarith only [h,herr,hscale,habs]
  have heq : f x-f y = L v+R := by dsimp [R]; abel
  rw [heq,saddlePairing_add_right]
  have hl := hlinear v
  change saddlePairing (G v) (L v)+saddlePairing (G v) R ≤ -((κ/2)*‖v‖^2)
  linarith only [hl,herr']

/-- The actual nonlinear response field inherits strict quadratic dissipation
for differences of any two sufficiently nearby points. -/
theorem middle_nonlinear_pair_dissipation (e z H : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ η δ : ℝ, 0 < η ∧ 0 < δ ∧ ∀ x y : SaddleVector,
      dist x ![60/(z+2),z,H,0] < δ → dist y ![60/(z+2),z,H,0] < δ →
      saddlePairing (saddleGradient e z (x-y))
        (responseCoordinateField e x-responseCoordinateField e y) ≤ -(η*‖x-y‖^2) := by
  let B := 60/(z+2)
  let a := 1+2*e*responseA e B
  let p : SaddleVector := ![B,z,H,0]
  let L : SaddleVector →L[ℝ] SaddleVector :=
    (responseCoordinateLinear B z (responseSlope e B) a).toContinuousLinearMap
  let G : SaddleVector →L[ℝ] SaddleVector := (saddleGradient e z).toContinuousLinearMap
  have hB : B ∈ Icc (2:ℝ) 34 :=
    curve_B_bounds z ⟨by linarith [hz.1],by linarith [hz.2]⟩
  obtain ⟨hAl,hAu⟩ := response_bounds e B he hu hB.1 hB.2
  have hEl := mul_le_mul_of_nonneg_left hAl he
  have hEu := mul_le_mul_of_nonneg_left hAu he
  have ha : 99/100 ≤ a := by dsimp [a]; nlinarith
  have ha' : a ≤ 101/100 := by dsimp [a]; nlinarith
  have hF : 60-(2+p 1)*p 0 = 0 := by
    have hd : z+2 ≠ 0 := by linarith [hz.1]
    dsimp [p,B]
    field_simp
    ring
  have hd : HasStrictFDerivAt (responseCoordinateField e) L p :=
    responseCoordinateField_hasStrictFDerivAt e p he hu hB (by rfl) hF
  obtain ⟨κ,hκ,hlin⟩ := middle_quadratic_rate_coercive e z he hu hz
  have hlinear : ∀ v, saddlePairing (G v) (L v) ≤ -(κ*‖v‖^2) := by
    intro v
    change saddlePairing (saddleGradient e z v)
      (responseCoordinateLinear (60/(z+2)) z (responseSlope e (60/(z+2))) a v) ≤ _
    rw [saddleGradient_linear_rate]
    exact hlin a ha ha' v
  obtain ⟨δ,hδ,hpair⟩ := strict_linear_dissipation_persists
    (responseCoordinateField e) G L p hd κ hκ hlinear
  exact ⟨κ/2,δ,by positivity,hδ,hpair⟩

end CoreCouplingGlobal
