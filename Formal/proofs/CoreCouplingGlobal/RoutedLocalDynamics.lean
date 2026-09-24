import proofs.CoreCouplingGlobal.RoutedSource
import proofs.CoreCouplingCAC.Cutoff
import proofs.CoreCouplingCAC.EnergyCoordinates
import proofs.CoreCouplingCAC.Convergence

open Filter Topology
namespace CoreCouplingGlobal
open CoreCouplingCAC

noncomputable def routedDynamics (e g : ℝ) (t : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![33-t 0-e*(t 1+(t 0+t 1)^2),
    -27-t 0-(3-g+g*t 2+e)*t 1-e*(t 0+t 1)^2,
    g*t 0+g*(1+t 2)*t 1-16*t 2-4*(t 2)^2+3*t 3,
    16*t 2+2*(t 2)^2-(20001/10000)*t 3]
noncomputable def routedJacobian (e g : ℝ) (t : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  ![![-1-2*e*(t 0+t 1),-e*(1+2*(t 0+t 1)),0,0],
    ![-1-2*e*(t 0+t 1),-3+g-g*t 2-e-2*e*(t 0+t 1),-g*t 1,0],
    ![g,g*(1+t 2),g*t 1-16-8*t 2,3],
    ![0,0,16+4*t 2,-20001/10000]]

theorem routed_dynamics_source (e g : ℝ) (x : State) :
    routedDynamics e g (transform x) =
      ![fA (flagshipRates e) x.A x.B (1-g+g*x.z)+fB (flagshipRates e) x.A x.B (1-g+g*x.z),
        -fB (flagshipRates e) x.A x.B (1-g+g*x.z),routedZ e g x,
        fH (flagshipRates e) x.z x.H] := by
  funext i
  fin_cases i <;> norm_num [routedDynamics,transform,fA,fB,fH,routedZ,flagshipRates,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] <;> ring

theorem routed_midpoint_secant (e g : ℝ) (x y : Fin 4 → ℝ) (i : Fin 4) :
    routedDynamics e g x i-routedDynamics e g y i =
      ∑ j : Fin 4, routedJacobian e g (fun k => (x k+y k)/2) i j*(x j-y j) := by
  fin_cases i <;> simp [routedDynamics,routedJacobian,Fin.sum_univ_succ] <;> ring

theorem routed_stationary_transformed (e g : ℝ) (x : State) (h : RoutedStationary e g x) :
    routedDynamics e g (transform x) = 0 := by
  rw [routed_dynamics_source]
  rcases h with ⟨hA,hB,hz,hH⟩
  simp [hA,hB,hz,hH]

noncomputable def routedEnergyRate (e g : ℝ) (L R c x : Fin 4 → ℝ) : ℝ :=
  ∑ i : Fin 4, 2*(L i/R i)*(x i-c i)*routedDynamics e g x i

theorem routed_nonlinear_energy_bound (e g : ℝ) (M : Fin 4 → Fin 4 → ℝ)
    (L R c x : Fin 4 → ℝ) (κ : ℝ)
    (hL : ∀ i, 0 < L i) (hR : ∀ i, 0 < R i)
    (hc : routedDynamics e g c = 0)
    (hdiag : ∀ i, routedJacobian e g (fun k => (x k+c k)/2) i i ≤ M i i)
    (hoff : ∀ i j, i ≠ j → |routedJacobian e g (fun k => (x k+c k)/2) i j| ≤ M i j)
    (hrow : ∀ i, L i*(∑ j, M i j*R j)+R i*(∑ j, M j i*L j) ≤
      -κ*(L i*R i)) :
    routedEnergyRate e g L R c x ≤ -κ*energy L R c x := by
  have h := comparison_energy_bound
    (routedJacobian e g (fun k => (x k+c k)/2)) M L R (fun i => (x i-c i)/R i) κ
    hL hR hdiag hoff hrow
  have hd : ∀ i, routedDynamics e g x i =
      ∑ j : Fin 4, routedJacobian e g (fun k => (x k+c k)/2) i j*(x j-c j) := by
    intro i
    have hs := routed_midpoint_secant e g x c i
    simpa [hc] using hs
  have he : routedEnergyRate e g L R c x =
      ∑ i : Fin 4, ∑ j : Fin 4,
        2*L i*routedJacobian e g (fun k => (x k+c k)/2) i j*R j*((x i-c i)/R i)*((x j-c j)/R j) := by
    unfold routedEnergyRate
    apply Finset.sum_congr rfl
    intro i _
    rw [hd,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hi : R i ≠ 0 := ne_of_gt (hR i)
    have hj : R j ≠ 0 := ne_of_gt (hR j)
    field_simp
  rw [he]
  convert h using 1
  congr 1
  unfold energy
  apply Finset.sum_congr rfl
  intro i _
  have hi : R i ≠ 0 := ne_of_gt (hR i)
  field_simp


theorem routed_dynamics_contDiff (e g : ℝ) : ContDiff ℝ 1 (routedDynamics e g) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> simp [routedDynamics] <;> fun_prop

theorem routed_global_extension (e g : ℝ) :
    ∃ f : (Fin 4 → ℝ) → (Fin 4 → ℝ),
      (∀ x, ‖x‖ ≤ 100 → f x = routedDynamics e g x) ∧
      (∀ x₀, ∃ x : ℝ → Fin 4 → ℝ, x 0 = x₀ ∧ ∀ t, HasDerivAt x (f (x t)) t) := by
  let b : ContDiffBump (0 : Fin 4 → ℝ) := ⟨100,200,by norm_num,by norm_num⟩
  let f : (Fin 4 → ℝ) → (Fin 4 → ℝ) := fun x => b x • routedDynamics e g x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (routed_dynamics_contDiff e g)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  refine ⟨f,?_,?_⟩
  · intro x hx
    have hb : b x = 1 := b.one_of_mem_closedBall (by simpa [b,dist_zero_right] using hx)
    simp [f,hb]
  · intro x₀
    exact bounded_lipschitz_global_solution f K ⟨max C 0,le_max_right _ _⟩ hK
      (fun x => (hC x).trans (le_max_left _ _)) x₀

end CoreCouplingGlobal
