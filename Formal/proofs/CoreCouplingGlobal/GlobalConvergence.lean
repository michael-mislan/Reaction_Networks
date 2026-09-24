import proofs.CoreCouplingGlobal.ResidualConvergence
import proofs.CoreCouplingGlobal.FiniteClusterLimit
import proofs.CoreCouplingGlobal.PositiveGlobalExistence
import proofs.CoreCouplingCAC.ExactClassification

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

theorem positive_of_stationary_responseBox (e : ℝ) (he : 0 ≤ e) (X : State)
    (hb : InResponseBox X) (hs : Stationary (flagshipRates e) X) : X.Positive := by
  obtain ⟨hA,hA',hB,hB',hz,hz',hH,hH'⟩ := hb
  obtain ⟨hfA,hfB,hfz,hfH⟩ := hs
  have heB := mul_nonneg he (by linarith : 0 ≤ X.B)
  have hzB := mul_nonneg hz (by linarith : 0 ≤ X.B)
  have hAp : 0 < X.A := by
    by_contra hn
    have hAz : X.A = 0 := by linarith
    dsimp [fA,flagshipRates] at hfA
    rw [hAz] at hfA
    nlinarith
  have hzp : 0 < X.z := by
    by_contra hn
    have hzz : X.z = 0 := by linarith
    dsimp [fZ,flagshipRates] at hfz
    rw [hzz] at hfz
    nlinarith
  have hHp : 0 < X.H := by
    by_contra hn
    have hHz : X.H = 0 := by linarith
    dsimp [fH,flagshipRates] at hfH
    rw [hHz] at hfH
    nlinarith
  exact ⟨hAp,by linarith,hzp,hHp⟩

theorem flagship_eq_vary (e : ℝ) : flagshipRates e = varyRates e := rfl

theorem trajectory_converges_to_positive_equilibrium (e : ℝ)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X) :
    ∃ s : State, s.Positive ∧ Stationary (flagshipRates e) s ∧
      Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s)) := by
  have he : 0 ≤ e := by linarith
  obtain ⟨a,b,c,ha,hb,hc,hsa,hsb,hsc,hab,hbc,hall⟩ := exactly_three_positive_equilibria e hl hu
  let S : Set ResponseVector := {encodeState a,encodeState b,encodeState c}
  have hS : S.Finite := by dsimp [S]; simp
  have hmem : ∀ᶠ t in atTop, encodeState (X t) ∈ responseBox := by
    filter_upwards [trajectory_eventually_responseBox e he hu X hX] with t ht
    exact (responseBox_iff _).2 (by simpa only [decode_encodeState] using ht)
  have hcont : ContinuousOn (fun t => encodeState (X t)) (Ici (0:ℝ)) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    apply HasDerivAt.continuousAt (f' := responseVectorField e (encodeState (X t)))
    apply hasDerivAt_pi.2
    intro i
    fin_cases i
    · exact hX.dA t ht
    · exact hX.dB t ht
    · exact hX.dz t ht
    · exact hX.dH t ht
  have hq := trajectory_residual_tendsto_zero e he hu X hX
  have hcluster : ∀ x ∈ responseBox,
      MapClusterPt x atTop (fun t => encodeState (X t)) → x ∈ S := by
    intro x hx hxc
    have hqcluster := hxc.continuousAt_comp (residualNorm_continuous e).continuousAt
    have hqzero : responseResidualNorm e (decodeState x) = 0 := by
      have hqt : Tendsto ((fun y => responseResidualNorm e (decodeState y)) ∘
          (fun t => encodeState (X t))) atTop (𝓝 0) := by
        simpa only [Function.comp_apply,decode_encodeState] using hq
      obtain ⟨ψ,hψ,hψtop⟩ := hqcluster.exists_seq_tendsto
      exact tendsto_nhds_unique hψ (hqt.comp hψtop)
    have hbox := (responseBox_iff x).1 hx
    have hstat := stationary_of_responseResidualNorm_zero e (decodeState x) he hu hbox hqzero
    have hpos := positive_of_stationary_responseBox e he (decodeState x) hbox hstat
    rw [flagship_eq_vary] at hstat
    have hcases := (hall (decodeState x) hpos hstat).1
    have henc : encodeState (decodeState x) = x := by funext i; fin_cases i <;> rfl
    rcases hcases with hh | hh | hh
    · have hh' := congrArg encodeState hh
      rw [henc] at hh'
      exact Or.inl hh'
    · have hh' := congrArg encodeState hh
      rw [henc] at hh'
      exact Or.inr (Or.inl hh')
    · have hh' := congrArg encodeState hh
      rw [henc] at hh'
      exact Or.inr (Or.inr hh')
  obtain ⟨x,hx,hlim⟩ := finite_cluster_limit responseBox S isCompact_Icc hS
    (fun t => encodeState (X t)) 0 hcont hmem hcluster
  rcases hx.2 with hh | hh | hh
  · exact ⟨a,ha,by simpa only [flagship_eq_vary] using hsa,hh ▸ hlim⟩
  · exact ⟨b,hb,by simpa only [flagship_eq_vary] using hsb,hh ▸ hlim⟩
  · exact ⟨c,hc,by simpa only [flagship_eq_vary] using hsc,hh ▸ hlim⟩

/-- Every positive initial state has a global positive literal solution, and that solution converges. -/
theorem global_positive_convergent_solution (e : ℝ)
    (hl : (1/200000:ℝ) ≤ e) (hu : e ≤ 1/50000) (x₀ : State) (hx₀ : x₀.Positive) :
    ∃ X : ℝ → State, X 0 = x₀ ∧ IsPositiveTrajectory e X ∧
      ∃ s : State, s.Positive ∧ Stationary (flagshipRates e) s ∧
        Tendsto (fun t => encodeState (X t)) atTop (𝓝 (encodeState s)) := by
  obtain ⟨X,hX0,hX⟩ := positive_global_solution e (by linarith) hu x₀ hx₀
  exact ⟨X,hX0,hX,trajectory_converges_to_positive_equilibrium e hl hu X hX⟩

end CoreCouplingGlobal
