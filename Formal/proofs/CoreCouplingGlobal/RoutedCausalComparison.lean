import proofs.CoreCouplingGlobal.RoutedWeakExistence
import proofs.CoreCouplingGlobal.RoutedBistability

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

theorem routed_productivity_from_capacity (e g : ℝ) (he : 0 < e)
    (hg : 0 < g) (hcap : 3*e < 2*g) :
    ∃ x : State, x.Positive ∧
      CoreProductive (routedCurrent (flagshipRates e) g x 0)
        (routedCurrent (flagshipRates e) g x 5) ∧
      CoreProductive (routedCurrent (flagshipRates e) g x 1)
        (routedCurrent (flagshipRates e) g x 2) := by
  have hq : 0 < 3*e/(2*g) := by positivity
  have hqu : 3*e/(2*g) < 1 := (div_lt_one (by positivity)).2 hcap
  let z : ℝ := (1-3*e/(2*g))/2
  have hz : 0 < z := by dsimp [z]; linarith
  have hzu : z < 1/2 := by dsimp [z]; linarith
  let x : State := ⟨1,2,z,8*z⟩
  obtain ⟨h₀,h₅,h₁,h₂⟩ := routed_core_current_formulas e g x
  have hj : g*(x.A-x.B*x.z) = 3*e/2 := by
    dsimp [x,z]
    field_simp
    ring
  refine ⟨x,⟨by norm_num [x],by norm_num [x],hz,by dsimp [x]; positivity⟩,?_,?_⟩
  · rw [h₀,h₅,hj]
    dsimp [CoreProductive,x]
    constructor <;> nlinarith
  · rw [h₁,h₂]
    dsimp [CoreProductive,x]
    have hpos := mul_pos hz (show 0 < 2-z by linarith)
    have hz2 := sq_pos_of_pos hz
    constructor <;> nlinarith

theorem routed_core_certificate_from_capacity (e g : ℝ)
    (he : 0 < e) (hg : 0 < g) (hgu : g < 1) (hcap : 3*e < 2*g) :
    RoutedCoreCertificate e g := by
  have hp : (flagshipRates e).Positive := by
    norm_num [Rates.Positive,flagshipRates]
    exact he
  have hrate : ∀ r : Fin 8, 0 < routedForward (flagshipRates e) g r ∧
      (r ≠ 6 → 0 < routedReverse (flagshipRates e) g r) := by
    intro r
    constructor
    · fin_cases r <;> norm_num [routedForward,flagshipRates] <;> linarith
    · intro hr
      fin_cases r
      all_goals simp_all [routedReverse,flagshipRates,Fin.ext_iff]
  exact ⟨hp,routed_AB_core false,routed_AB_core true,routed_ZH_core,
    by unfold AutonomousRestriction; decide,
    gain_two_core_reaction_minimal,core_species_minimal,
    routed_productivity_from_capacity e g he hg hcap,routed_isolated_productive_state e he,
    routed_mass_balance,hrate,routed_reversible_ratios (flagshipRates e) hp g hg hgu,
    rfl,fork_capacity_preserved (flagshipRates e) g⟩

/-- Weak dynamic feedback retains positive uniqueness without removing either core
or changing the drain regime. Both cores have a common productive realization. -/
theorem admissible_weak_routing_unique (e g : ℝ)
    (he : 0 < e) (heu : e ≤ 1/50000)
    (hg : (1/100:ℝ) ≤ g) (hgu : g ≤ 1/10) :
    RoutedCoreCertificate e g ∧ (∃! x : State, x.Positive ∧ RoutedStationary e g x) := by
  exact ⟨routed_core_certificate_from_capacity e g he (by linarith) (by linarith)
    (by linarith),routed_weak_exactly_one e g he.le heu (by linarith) hgu⟩

/-- A nonzero-coupling one-versus-bistable comparison at identical intrinsic rates.
The two coupled systems both satisfy the same literal core certificate. -/
theorem admissible_feedback_creates_bistability (e weak strong : ℝ)
    (hstrong : (e,strong) ∈ routedBistableRegion)
    (hw : (1/100:ℝ) ≤ weak) (hwu : weak ≤ 1/10) :
    (RoutedCoreCertificate e weak ∧
      (∃! x : State, x.Positive ∧ RoutedStationary e weak x)) ∧
    RoutedCoreCertificate e strong ∧
    (∃! x : State, x.Positive ∧ RoutedStationary e 0 x) ∧
    ∃ x y : State, x.Positive ∧ y.Positive ∧ RoutedStationary e strong x ∧
      RoutedStationary e strong y ∧ x.z < y.z ∧
      RoutedSelected e strong lowLeft lowRight x ∧
      RoutedSelected e strong highLeft highRight y := by
  have he : 0 < e := by have h := hstrong.1.1; linarith
  have heu : e ≤ 1/50000 := by have h := hstrong.1.2; linarith
  exact ⟨admissible_weak_routing_unique e weak he heu hw hwu,
    routed_causal_bistability e strong hstrong⟩

end CoreCouplingGlobal
