import proofs.CoreCouplingGlobal.BasinManifoldChart
import proofs.CoreCouplingGlobal.UnstableDestinations
import proofs.CoreCouplingGlobal.PhysicalSpectrum
import proofs.CoreCouplingGlobal.NonemptySelector

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter
open scoped Topology ContDiff

/-- G at its literal flagship scope. The fields retain global existence and
all-trajectory convergence, exact basin boundaries, actual analytic ambient and
invariant charts, spectral tangency/coverage, unstable destinations, full physical
spectra and a nonempty concentration-space selection rule. -/
structure FlagshipGResolution (e : ℝ) : Prop where
  classified_equilibria :
    ∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
          Stationary (varyRates e) x ∧ Stationary (varyRates e) y ∧ Stationary (varyRates e) w ∧
          x.z < y.z ∧ y.z < w.z ∧ Set.Icc (9/10:ℝ) (11/10) x.z ∧
          Set.Icc (19/10:ℝ) (21/10) y.z ∧ Set.Icc (29/10:ℝ) (31/10) w.z ∧
          ∀ s : State, s.Positive → Stationary (varyRates e) s →
            (s = x ∨ s = y ∨ s = w) ∧ (countPoly e).derivative.eval (rootParameter s) ≠ 0
  global_existence :
    ∀ x₀ : State, x₀.Positive →
    ∃ X : ℝ → State, X 0 = x₀ ∧ IsPositiveTrajectory e X ∧
          ∃ s : State, s.Positive ∧ Stationary (flagshipRates e) s ∧
            Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s))
  all_trajectory_limits :
    ∀ X : ℝ → State, IsPositiveTrajectory e X →
    ∃ s : State, s.Positive ∧ Stationary (flagshipRates e) s ∧
          Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s))
  basin_boundaries :
    ∃ low mid high : State, low.Positive ∧ mid.Positive ∧ high.Positive ∧
          Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
          Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
          IsOpen (positiveBasin e low) ∧ IsOpen (positiveBasin e high) ∧
          Disjoint (positiveBasin e low) (positiveBasin e high) ∧
          frontier (positiveBasin e low) ∩ positiveDomain = positiveBasin e mid ∧
          frontier (positiveBasin e high) ∩ positiveDomain = positiveBasin e mid
  middle_ambient_charts :
    ∀ s : State, s.Positive → Stationary (flagshipRates e) s →
      s.z ∈ Icc (19/10:ℝ) (21/10) →
    ∀ x : ResponseVector, x ∈ positiveBasin e s →
    ∃ H : OpenPartialHomeomorph ResponseVector ResponseVector,
          x ∈ H.source ∧ ContDiffOn ℝ ω H H.source ∧ ContDiffOn ℝ ω H.symm H.target ∧
          ∀ y ∈ H.source, y ∈ positiveDomain ∧ (y ∈ positiveBasin e s ↔ H y 3=0)
  stable_patch_and_coverage :
    ∀ s : State, s.Positive → Stationary (flagshipRates e) s →
      s.z ∈ Icc (19/10:ℝ) (21/10) →
    ∃ μ : Fin 4 → ℝ, ∃ C : ResponseVector ≃L[ℝ] ResponseVector,
        MiddlePerronCoordinates e s μ C ∧ ∃ φ : StableData → ResponseVector,
        ∃ U : Set StableData, ∃ δ : ℝ,
          IsOpen U ∧ 0 ∈ U ∧ 0 < δ ∧ φ 0=encodeState s ∧
          HasFDerivAt φ (C.toContinuousLinearMap.comp stableInclusion) 0 ∧
          ContDiffOn ℝ ω φ U ∧ InjOn φ U ∧
          (∀ ξ ∈ U, middleStableProjection C s (φ ξ)=ξ) ∧
          (∀ ξ ∈ U, ∃ Y : ℝ → ResponseVector, Y 0=φ ξ ∧
            (∀ t, 0 ≤ t → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
            (∀ t, 0 ≤ t → Y t ∈ positiveDomain ∧ ‖C.symm (Y t-encodeState s)‖ < δ) ∧
            Tendsto Y atTop (𝓝 (encodeState s))) ∧
          (∀ ξ ∈ U, φ ξ ∈ positiveBasin e s) ∧
          ∀ Z : ℝ → ResponseVector,
            (∀ t, 0 ≤ t → HasDerivAt Z (responseVectorField e (Z t)) t) →
            (∀ t, 0 ≤ t → ‖C.symm (Z t-encodeState s)‖ < δ) →
            ∀ T, 0 ≤ T → middleStableProjection C s (Z T) ∈ U →
            Z T=φ (middleStableProjection C s (Z T))
  actual_unstable_destinations :
    ∃ low mid high : State, low.Positive ∧ mid.Positive ∧ high.Positive ∧
          Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
          Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
          ∃ μ : Fin 4 → ℝ, ∃ C : ResponseVector ≃L[ℝ] ResponseVector,
          MiddlePerronCoordinates e mid μ C ∧ ∃ φ : ℝ → ResponseVector, ∃ r δ b : ℝ,
            0 < r ∧ 0 < δ ∧ b ≠ 0 ∧ b=C (unstableInclusion 1) 1 ∧ φ 0=encodeState mid ∧
            HasFDerivAt φ (C.toContinuousLinearMap.comp unstableInclusion) 0 ∧
            ContDiffOn ℝ ω φ (Ioo (-r) r) ∧ InjOn φ (Ioo (-r) r) ∧
            (∀ a ∈ Ioo (-r) r, C.symm (φ a-encodeState mid) 3=a) ∧
            (∀ a ∈ Ioo (-r) r, ∃ Y : ℝ → ResponseVector, Y 0=φ a ∧
              (∀ t, t ≤ 0 → HasDerivAt Y (responseVectorField e (Y t)) t) ∧
              (∀ t, t ≤ 0 → Y t ∈ positiveDomain ∧ ‖C.symm (Y t-encodeState mid)‖ < δ) ∧
              Tendsto (fun t => Y (-t)) atTop (𝓝 (encodeState mid))) ∧
            (∀ a ∈ Ioo (-r) r, a ≠ 0 → ∃ X : ℝ → State,
              X 0=decodeState (φ a) ∧ IsPositiveTrajectory e X ∧
              (0 < a*b → Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState low))) ∧
              (a*b < 0 → Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState high)))) ∧
            ∀ Z : ℝ → ResponseVector,
              (∀ t, t ≤ 0 → HasDerivAt Z (responseVectorField e (Z t)) t) →
              (∀ t, t ≤ 0 → ‖C.symm (Z t-encodeState mid)‖ < δ) →
              ∀ T, T ≤ 0 → C.symm (Z T-encodeState mid) 3 ∈ Ioo (-r) r →
                Z T=φ (C.symm (Z T-encodeState mid) 3)
  middle_spectrum :
    ∀ s : State, s.Positive → Stationary (flagshipRates e) s →
      s.z ∈ Icc (19/10:ℝ) (21/10) →
    ∃ a b c d : ℝ, a ∈ Ioo (-80:ℝ) (-10) ∧ b ∈ Ioo (-10:ℝ) (-2) ∧
          c ∈ Ioo (-2:ℝ) (-(1/2)) ∧ d ∈ Ioo (0:ℝ) (1/10) ∧
          ∀ ξ : ℂ, ξ ∈ spectrum ℂ ((physicalJacobian e (encodeState s)).map Complex.ofRealHom) ↔
            ξ = (a:ℂ) ∨ ξ = (b:ℂ) ∨ ξ = (c:ℂ) ∨ ξ = (d:ℂ)
  outer_spectrum :
    ∀ s : State, s.Positive → Stationary (flagshipRates e) s →
      (s.z ∈ Icc (9/10:ℝ) (11/10) ∨ s.z ∈ Icc (29/10:ℝ) (31/10)) →
    ∃ a b c d : ℝ, a ∈ Ioo (-80:ℝ) (-10) ∧ b ∈ Ioo (-10:ℝ) (-2) ∧
          c ∈ Ioo (-2:ℝ) (-(1/2)) ∧ d ∈ Ioo (-(1/2):ℝ) 0 ∧
          ∀ ξ : ℂ, ξ ∈ spectrum ℂ ((physicalJacobian e (encodeState s)).map Complex.ofRealHom) ↔
            ξ = (a:ℂ) ∨ ξ = (b:ℂ) ∨ ξ = (c:ℂ) ∨ ξ = (d:ℂ)
  physical_derivative :
    ∀ x : ResponseVector,
    HasFDerivAt (responseVectorField e) (physicalJacobian e x).toLin'.toContinuousLinearMap x
  initial_selector :
    ∃ p : PotentialPrimitives e, ∃ low mid high : State,
          low.Positive ∧ mid.Positive ∧ high.Positive ∧
          Stationary (flagshipRates e) low ∧ Stationary (flagshipRates e) mid ∧
          Stationary (flagshipRates e) high ∧ low.z < mid.z ∧ mid.z < high.z ∧
          ∀ X : ℝ → State, IsPositiveTrajectory e X → InSelectionRegion (X 0) →
            statePotential e p (X 0) < statePotential e p mid →
            ((X 0).B < mid.B → Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState high))) ∧
            (mid.B < (X 0).B → Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState low)))
  nonempty_selected_families :
    ∃ low high : State, low.Positive ∧ high.Positive ∧ low.z < high.z ∧
          ∃ δ : ℝ, 0 < δ ∧ ∀ ε ∈ Ioo (0:ℝ) δ,
            (perturbA low ε).Positive ∧ perturbA low ε ≠ low ∧
            (perturbA high ε).Positive ∧ perturbA high ε ≠ high ∧
            (∀ X : ℝ → State, IsPositiveTrajectory e X → X 0 = perturbA low ε →
              Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState low))) ∧
            (∀ X : ℝ → State, IsPositiveTrajectory e X → X 0 = perturbA high ε →
              Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState high)))

/-- The complete flagship global-selection endpoint on the working interval. -/
theorem flagship_G_endpoint (e : ℝ) (hl : (1/200000:ℝ) ≤ e)
    (hu : e ≤ 1/50000) : FlagshipGResolution e := by
  have he : 0 ≤ e := by linarith
  exact {
    classified_equilibria := exactly_three_bracketed_equilibria e hl hu
    global_existence := fun x hx => global_positive_convergent_solution e hl hu x hx
    all_trajectory_limits := fun X hX => trajectory_converges_to_positive_equilibrium e hl hu X hX
    basin_boundaries := outer_basin_boundaries_equal_middle e hl hu
    middle_ambient_charts := fun s hs hss hz x hx =>
      middle_basin_analytic_manifold_chart e hl hu s hs hss hz x hx
    stable_patch_and_coverage := fun s hs hss hz => middle_stable_patch_coverage e he hu s hs hss hz
    actual_unstable_destinations := middle_actual_unstable_branch_destinations e hl hu
    middle_spectrum := fun s hs hss hz => middle_physical_spectrum e he hu s hs hss hz
    outer_spectrum := fun s hs hss hz => outer_physical_spectrum e he hu s hs hss hz
    physical_derivative := physicalJacobian_hasFDerivAt e
    initial_selector := initial_state_sublevel_selector e hl hu
    nonempty_selected_families := nontrivial_selected_families e hl hu }

end CoreCouplingGlobal
