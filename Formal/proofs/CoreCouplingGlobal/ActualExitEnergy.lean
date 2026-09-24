import proofs.CoreCouplingGlobal.FirstExit
import proofs.CoreCouplingGlobal.ExitEnergy

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

theorem perturbedSaddleQuadratic_sub_swap (e z α : ℝ) (x y : SaddleVector) :
    perturbedSaddleQuadratic e z α (y-x) = perturbedSaddleQuadratic e z α (x-y) := by
  simp [perturbedSaddleQuadratic,saddleQuadraticValue,responseQuadratic,saddlePairing,Fin.sum_univ_succ]
  ring

/-- The same cone coefficient supplies actual first exit and energy below
the middle stationary response point, at every sufficiently small radius. -/
theorem middle_actual_first_exit_below_energy (e z : ℝ) (P : PotentialPrimitives e)
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
        (∀ t ∈ Ico 0 τ, dist (saddleCoordinates e (Y t)) p < r) ∧
        (∀ t ∈ Icc 0 τ, pairConeValue e z α X Y t < 0) ∧
        (∀ t ∈ Icc 0 τ, (X t).B ≠ (Y t).B) ∧
        responsePotential e P (Y τ).B (Y τ).z (Y τ).H
          ((Y τ).A+(Y τ).B-responseTotal e (Y τ).B) <
          responsePotential e P (p 0) (p 1) (p 2) (p 3) := by
  dsimp only
  let H := (16*z+2*z^2)/(20001/10000)
  let p : SaddleVector := ![60/(z+2),z,H,0]
  obtain ⟨α,d,hα,hd,hv,hexit⟩ := middle_first_exit_at_radius e z H he hu hz
  obtain ⟨δ,θ,hδ,hθ,hθh,henergy⟩ := negative_cone_exit_energy e z α P he hu hz hZ hα
  refine ⟨α,min d δ,θ,hα,lt_min hd hδ,hθ,hθh,hv,?_⟩
  intro r hr hrd X Y hX hY hstay hY0 hstart
  have hhalf : ∀ t : ℝ, 0 ≤ t → dist (saddleCoordinates e (X t)) p < r/2 := by
    intro t ht
    have hh := hstay t ht
    change dist (saddleCoordinates e (X t)) p < θ*r at hh
    have hm := mul_le_mul_of_nonneg_right hθh hr.le
    linarith
  obtain ⟨τ,hτ,hlevel,hbefore,hnegative,hB⟩ :=
    hexit r hr (hrd.trans_le (min_le_left _ _)) X Y hX hY hhalf hY0 hstart
  refine ⟨τ,hτ,hlevel,hbefore,fun t ht => (hnegative t ht).2,hB,?_⟩
  have hcone : perturbedSaddleQuadratic e z α
      (saddleCoordinates e (Y τ)-saddleCoordinates e (X τ)) ≤ 0 := by
    rw [perturbedSaddleQuadratic_sub_swap]
    exact ((hnegative τ ⟨hτ.le,le_rfl⟩).2).le
  exact henergy r hr (hrd.trans_le (min_le_right _ _))
    (saddleCoordinates e (X τ)) (saddleCoordinates e (Y τ)) (hstay τ hτ.le) hlevel hcone

end CoreCouplingGlobal
