import proofs.CoreCouplingGlobal.ExitSide
import proofs.CoreCouplingGlobal.SelectionRegion

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

/-- The half-unit response neighborhood of a middle response point lies in
the actual selector's concentration region, not only the primitive domains. -/
theorem middle_response_neighborhood_selection_region (e z : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10))
    (s : State)
    (hx : dist (saddleCoordinates e s)
      ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0] < 1/2) :
    InSelectionRegion s := by
  let p : SaddleVector := ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0]
  have hbox := middle_potential_unit_box z hz (saddleCoordinates e s)
    (hx.trans (by norm_num))
  have hB : s.B ∈ Icc (2:ℝ) 34 := hbox.1
  have hzs : s.z ≤ 12 := hbox.2.1.2
  have hc (i : Fin 4) : |saddleCoordinates e s i-p i| < 1/2 :=
    lt_of_le_of_lt (norm_le_pi_norm (saddleCoordinates e s-p) i) hx
  have hHr := (abs_lt.mp (hc 2)).2
  have hrr := (abs_lt.mp (hc 3)).2
  change s.H-(16*z+2*z^2)/(20001/10000) < 1/2 at hHr
  change s.A+s.B-responseTotal e s.B-0 < 1/2 at hrr
  have hz0 : 0 ≤ z := by linarith [hz.1]
  have hzsq := pow_le_pow_left₀ hz0 hz.2 2
  have hHu : (16*z+2*z^2)/(20001/10000) ≤ (40:ℝ) :=
    (div_le_iff₀ (by norm_num)).2 (by nlinarith [hz.2])
  have hquad := response_quadratic e s.B he hu hB.1 hB.2
  have hnon := mul_nonneg he (sq_nonneg (responseA e s.B))
  have heB := mul_le_mul hu hB.2 (by linarith [hB.1] : 0 ≤ s.B) (by norm_num : (0:ℝ) ≤ 1/50000)
  dsimp [responseTotal] at hrr
  exact ⟨by linarith,by linarith,hzs,hB.1⟩

/-- Actual local departure supplies all concentration, energy and side
conditions needed to apply the existing sublevel selector at the exit. -/
theorem middle_actual_exit_selector_conditions (e z : ℝ) (P : PotentialPrimitives e)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10))
    (hZ : responseTotal e (60/(z+2))-(1+z)*(60/(z+2))-16*z-4*z^2+
      3*((16*z+2*z^2)/(20001/10000)) = 0) :
    let p : SaddleVector := ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0]
    ∃ α δ θ : ℝ, 0 < α ∧ 0 < δ ∧ 0 < θ ∧ θ ≤ 1/2 ∧
      perturbedSaddleQuadratic e z α
        ![-(60/(z+2))/(z+2),1,(16+4*z)/(20001/10000),0] < 0 ∧
      ∀ r : ℝ, 0 < r → r < δ → ∀ X Y : ℝ → State,
      IsPositiveTrajectory e X → IsPositiveTrajectory e Y →
      (∀ t : ℝ, 0 ≤ t → dist (saddleCoordinates e (X t)) p < θ*r) →
      dist (saddleCoordinates e (Y 0)) p < r → pairConeValue e z α X Y 0 < 0 →
      ∃ τ : ℝ, 0 < τ ∧ dist (saddleCoordinates e (Y τ)) p = r ∧
        InSelectionRegion (Y τ) ∧
        responsePotential e P (Y τ).B (Y τ).z (Y τ).H
          ((Y τ).A+(Y τ).B-responseTotal e (Y τ).B) <
          responsePotential e P (p 0) (p 1) (p 2) (p 3) ∧
        ((Y τ).B < p 0 ↔ (Y 0).B < (X 0).B) ∧
        (p 0 < (Y τ).B ↔ (X 0).B < (Y 0).B) := by
  dsimp only
  let p : SaddleVector := ![60/(z+2),z,(16*z+2*z^2)/(20001/10000),0]
  obtain ⟨α,d,θ₀,hα,hd,hθ₀,hθ₀h,hv,hexit⟩ :=
    middle_actual_first_exit_below_energy e z P he hu hz hZ
  let β := α/(2*localForkSlope e (60/(z+2)) z*(60/(z+2)))
  have hβ : 0 < β := middle_cone_side_coefficient_pos e z α he hu hz hα
  let θ := min θ₀ (β/4)
  have hθ : 0 < θ := lt_min hθ₀ (by positivity)
  have hθ₁ : θ ≤ θ₀ := min_le_left _ _
  have hθ₂ : θ ≤ β/4 := min_le_right _ _
  have hθh : θ ≤ 1/2 := hθ₁.trans hθ₀h
  refine ⟨α,min d (1/2),θ,hα,lt_min hd (by norm_num),hθ,hθh,hv,?_⟩
  intro r hr hrd X Y hX hY hstay hY0 hstart
  have hstay' : ∀ t : ℝ, 0 ≤ t → dist (saddleCoordinates e (X t)) p < θ₀*r := by
    intro t ht
    exact (hstay t ht).trans_le (mul_le_mul_of_nonneg_right hθ₁ hr.le)
  obtain ⟨τ,hτ,hlevel,_hbefore,hnegative,hB,henergy⟩ :=
    hexit r hr (hrd.trans_le (min_le_left _ _)) X Y hX hY hstay' hY0 hstart
  have hregion := middle_response_neighborhood_selection_region e z he hu hz (Y τ)
    (by rw [hlevel]; exact hrd.trans_le (min_le_right _ _))
  have hs := cone_exit_initial_side e z α r θ τ p he hu hz hα hr hτ.le hθh hθ₂
    X Y hX hY hB (hstay τ hτ.le) hlevel (hnegative τ ⟨hτ.le,le_rfl⟩).le
  exact ⟨τ,hτ,hlevel,hregion,henergy,hs.1,hs.2⟩

end CoreCouplingGlobal
