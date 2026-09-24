import proofs.CoreCouplingGlobal.TrajectoryActivity

open Filter Topology Set
namespace CoreCouplingGlobal
open CoreCouplingCAC

/-- Binary actual-current signature: AB is not strictly productive; ZH is,
and both ZH net reaction currents have the required orientations. -/
def ActivitySignature (e : ℝ) (x : State) : Prop :=
  ¬ CoreProductive (sourceCurrent (flagshipRates e) x 0)
    (sourceCurrent (flagshipRates e) x 5) ∧
  CoreProductive (sourceCurrent (flagshipRates e) x 1)
    (sourceCurrent (flagshipRates e) x 2) ∧
  0 < sourceCurrent (flagshipRates e) x 1 ∧
  0 < sourceCurrent (flagshipRates e) x 2

theorem stationary_activity_signature (e : ℝ)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000)
    (s : State) (hs : s.Positive) (hss : Stationary (flagshipRates e) s) :
    ActivitySignature e s := by
  obtain ⟨hb,hz,hh⟩ := stationary_activity_margins e hl hu s hs hss
  obtain ⟨hab,hzh⟩ := actual_current_productivity_iff (flagshipRates e) s
  have hp := hzh.2 ⟨by linarith,by linarith⟩
  exact ⟨fun h => by have hh := (hab.1 h).2; linarith,hp,
    productive_currents_positive _ _ hp⟩

/-- The selected equilibrium cannot be recovered from these two activity labels.
The z concentration separates two positive stationary states with identical labels. -/
theorem distinct_equilibria_same_activity (e : ℝ)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) :
    ∃ x y : State, x.Positive ∧ y.Positive ∧
      Stationary (flagshipRates e) x ∧ Stationary (flagshipRates e) y ∧
      x.z < y.z ∧ ActivitySignature e x ∧ ActivitySignature e y := by
  obtain ⟨x,y,w,hx,hy,hw,hsx,hsy,hsw,hxy,hyw,hbx,hby,hbw⟩ :=
    creation_interval_bracketed e hl hu
  have hsx' : Stationary (flagshipRates e) x := hsx
  have hsw' : Stationary (flagshipRates e) w := hsw
  exact ⟨x,w,hx,hw,hsx',hsw',lt_trans hxy hyw,
    stationary_activity_signature e hl hu x hx hsx',
    stationary_activity_signature e hl hu w hw hsw'⟩

/-- A's trajectory endpoint uses actual global solutions and actual net currents;
no convergence, activity or residence conclusion is supplied as a hypothesis. -/
theorem flagship_activity_endpoint (e : ℝ)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) :
    (∀ x₀ : State, x₀.Positive → ∃ X : ℝ → State, X 0 = x₀ ∧
      IsPositiveTrajectory e X ∧ ∃ s : State, s.Positive ∧
        Stationary (flagshipRates e) s ∧
        Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s)) ∧
        ActivitySignature e s ∧
        (∀ᶠ t in atTop, ActivitySignature e (X t)) ∧
        (∀ᶠ t in atTop, (coreAB (flagshipRates e) (X t)).2 < -3 ∧
          2 < (coreZH (flagshipRates e) (X t)).1 ∧
          (1/4000:ℝ) < (coreZH (flagshipRates e) (X t)).2)) ∧
    (∀ X : ℝ → State, IsPositiveTrajectory e X →
      ∀ η a b : ℝ, 0 < η → 0 ≤ a → a ≤ b → (X b).z ≤ 12 →
      (∀ t ∈ Icc a b, η ≤ (coreAB (flagshipRates e) (X t)).1 ∧
        η ≤ (coreAB (flagshipRates e) (X t)).2 ∧
        η ≤ (coreZH (flagshipRates e) (X t)).1) → b-a ≤ 3/η) ∧
    (∃ x y : State, x.Positive ∧ y.Positive ∧
      Stationary (flagshipRates e) x ∧ Stationary (flagshipRates e) y ∧
      x.z < y.z ∧ ActivitySignature e x ∧ ActivitySignature e y) := by
  refine ⟨?_,?_,distinct_equilibria_same_activity e hl hu⟩
  · intro x₀ hx₀
    obtain ⟨X,h0,hX,s,hs,hss,hlim⟩ := global_positive_convergent_solution e hl hu x₀ hx₀
    exact ⟨X,h0,hX,s,hs,hss,hlim,stationary_activity_signature e hl hu s hs hss,
      eventual_actual_core_signature e hl hu X hX,
      every_trajectory_eventual_activity e hl hu X hX⟩
  · intro X hX η a b hη ha hab hzb hprod
    exact simultaneous_productivity_duration e η a b hη ha hab X hX hzb hprod

end CoreCouplingGlobal
