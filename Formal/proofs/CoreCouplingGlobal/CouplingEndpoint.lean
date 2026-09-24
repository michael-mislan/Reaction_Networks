import proofs.CoreCouplingGlobal.RoutedCreationCriterion

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

def IsolatedModulesUnique (e : ℝ) : Prop :=
  (∃! u : ℝ × ℝ, 0 < u.1 ∧ 0 < u.2 ∧
    fA (flagshipRates e) u.1 u.2 1=0 ∧ fB (flagshipRates e) u.1 u.2 1=0) ∧
  (∃! u : ℝ × ℝ, 0 < u.1 ∧ 0 < u.2 ∧
    -16*u.1-4*u.1^2+3*u.2=0 ∧ fH (flagshipRates e) u.1 u.2=0)

/-- The explicit C scope: literal core admissibility, isolated existence/uniqueness,
weak-coupling uniqueness, actual strong-coupling attractors, and their mechanism. -/
structure RoutedCResolution (e g : ℝ) : Prop where
  cores : RoutedCoreCertificate e g
  isolated_modules : IsolatedModulesUnique e
  isolated_system : ∃! x : State, x.Positive ∧ RoutedStationary e 0 x
  weak_regime : ∀ weak ∈ Icc (1/100:ℝ) (1/10),
    RoutedCoreCertificate e weak ∧ (∃! x : State, x.Positive ∧ RoutedStationary e weak x)
  low_criterion : RoutedAttractorCriterion e g (9957/10000) (9959/10000)
    routedLowLower routedLowUpper lowLeft lowRight routedLowComparison
  high_criterion : RoutedAttractorCriterion e g (14881/5000) (14883/5000)
    routedHighLower routedHighUpper highLeft highRight routedHighComparison
  selected_states : ∃ x y : State, x.Positive ∧ y.Positive ∧ RoutedStationary e g x ∧
    RoutedStationary e g y ∧ x.z < y.z ∧ routedK y.z < routedK x.z ∧
    RoutedSelected e g lowLeft lowRight x ∧ RoutedSelected e g highLeft highRight y
  stationary_characterization : ∀ x : State,
    (x.Positive ∧ RoutedStationary e g x) ↔
      ∃ z : ℝ, 0 < z ∧ 0 < routedNumerA g z ∧ routedPoly e g z=0 ∧ x=routedLift g z
  monotone_load_uniqueness : ∀ S : Set ℝ, MonotoneOn routedK S →
    ∀ x y : State, x.Positive → y.Positive → RoutedStationary e g x →
      RoutedStationary e g y → x.z ∈ S → y.z ∈ S → x=y

theorem routed_C_resolution (e g : ℝ) (hp : (e,g) ∈ routedBistableRegion) :
    RoutedCResolution e g := by
  have he : 0 < e := by have h := hp.1.1; linarith
  have heu : e ≤ 1/50000 := by have h := hp.1.2; linarith
  have hg : 0 < g := by have h := hp.2.1; linarith
  have hlow := routed_low_creation_certificate e g hp.1.1.le hp.1.2.le hp.2.1.le hp.2.2.le
  have hhigh := routed_high_creation_certificate e g hp.1.1.le hp.1.2.le hp.2.1.le hp.2.2.le
  obtain ⟨x,y,hx,hy,hsx,hsy,hxy,hselx,hsely⟩ := routed_two_certificates_bistability e g
    (9957/10000) (9959/10000) (14881/5000) (14883/5000) (ne_of_gt hg)
    routedLowLower routedLowUpper routedHighLower routedHighUpper
    lowLeft lowRight highLeft highRight routedLowComparison routedHighComparison
    (by norm_num) hlow hhigh
  have hcore := routed_core_certificate_from_capacity e g he hg hp.2.2 (by
    have h := hp.2.1
    linarith)
  have hiso : ∃! x : State, x.Positive ∧ RoutedStationary e 0 x :=
    routed_weak_exactly_one e 0 he.le heu (by norm_num) (by norm_num)
  exact ⟨hcore,routed_isolated_modules_unique e he.le,hiso,
    fun weak hw => admissible_weak_routing_unique e weak he heu hw.1 hw.2,
    hlow,hhigh,⟨x,y,hx,hy,hsx,hsy,hxy,
      routed_multiplicity_requires_decreasing_load e g he.le hg hp.2.2.le x y hx hy hsx hsy hxy,
      hselx,hsely⟩,
    routed_positive_stationary_iff e g hg hp.2.2.le,
    routed_unique_on_monotone_load e g he.le hg hp.2.2.le⟩

theorem routed_positive_test_state : (⟨1,2,1,8⟩ : State).Positive := by
  norm_num [State.Positive]

/-- The two varying parameters change the actual transformed vector field at
one fixed positive concentration state; this family is not a relabeling. -/
theorem routed_parameter_field_injective :
    Function.Injective (fun p : ℝ × ℝ =>
      routedDynamics p.1 p.2 (transform (⟨1,2,1,8⟩ : State))) := by
  intro p q h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  norm_num [routedDynamics,transform,Matrix.cons_val_two] at h0 h2
  exact Prod.ext (by linarith only [h0]) (by linarith only [h2])

/-- C endpoint on a nonempty open family of distinct literal routed kinetics.
No universal arbitrary-module composition statement is asserted. -/
theorem core_coupling_C_endpoint :
    IsOpen routedBistableRegion ∧ routedBistableRegion.Nonempty ∧
    Function.Injective (fun p : ℝ × ℝ =>
      routedDynamics p.1 p.2 (transform (⟨1,2,1,8⟩ : State))) ∧
    ∀ p ∈ routedBistableRegion, RoutedCResolution p.1 p.2 :=
  ⟨routed_bistable_region_open_nonempty.1,routed_bistable_region_open_nonempty.2,
    routed_parameter_field_injective,fun p hp => routed_C_resolution p.1 p.2 hp⟩

end CoreCouplingGlobal
