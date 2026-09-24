import proofs.OverlappingSiphonInvasion.NormalizedCompact
import proofs.OverlappingSiphonInvasion.SourceFlowIdentities

noncomputable section
open Set
namespace OverlappingSiphonInvasion

private theorem lift_ode_dist (f : LiftState → LiftState) (K : NNReal)
    (hK : LipschitzWith K f) (X Y : ℝ → LiftState)
    (hX : ∀ t, 0 ≤ t → HasDerivAt X (f (X t)) t)
    (hY : ∀ t, 0 ≤ t → HasDerivAt Y (f (Y t)) t) (t : ℝ) (ht : 0 ≤ t) :
    dist (X t) (Y t) ≤ dist (X 0) (Y 0)*Real.exp (K*t) := by
  have hh := dist_le_of_trajectories_ODE_of_mem (v := fun _ => f)
    (s := fun _ => univ) (fun _ _ => hK.lipschitzOnWith)
    (fun s hs => (hX s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hX s hs.1).hasDerivWithinAt) (fun _ _ => mem_univ _)
    (fun s hs => (hY s hs.1).continuousAt.continuousWithinAt)
    (fun s hs => (hY s hs.1).hasDerivWithinAt) (fun _ _ => mem_univ _)
    (le_refl (dist (X 0) (Y 0))) t ⟨ht,le_rfl⟩
  simpa only [sub_zero] using hh

private theorem normalized_cutoff_flow (p : Rates) (ru rv rj R : ℝ) :
    ∃ f : LiftState → LiftState, ∃ K : NNReal, ∃ Φ : LiftState → ℝ → LiftState,
      LipschitzWith K f ∧
      (∀ z, ‖z‖ ≤ max R 1 → f z = normalizedField p ru rv rj z) ∧
      (∀ z, Φ z 0 = z) ∧
      (∀ z t, HasDerivAt (Φ z) (f (Φ z t)) t) ∧
      (∀ t, 0 ≤ t → Continuous (fun z => Φ z t)) := by
  let S := max R 1
  have hS : 0 < S := (by norm_num : (0:ℝ) < 1).trans_le (le_max_right _ _)
  let q : ContDiffBump (0:LiftState) := ⟨S,2*S,hS,by linarith⟩
  let f : LiftState → LiftState := fun z => q z • normalizedField p ru rv rj z
  have hs : HasCompactSupport f := q.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := q.contDiff.smul (normalizedField_contDiff p ru rv rj)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  let L : NNReal := ⟨max C 0,le_max_right _ _⟩
  have hL : ∀ z, ‖f z‖ ≤ L := fun z => (hC z).trans (le_max_left _ _)
  choose Φ hΦ0 hΦd using (fun z => CoreCouplingCAC.bounded_lipschitz_global_solution f K L hK hL z)
  refine ⟨f,K,Φ,hK,?_,hΦ0,hΦd,?_⟩
  · intro z hz
    have hq : q z = 1 := q.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
    simp only [f,hq,one_smul]
  · intro t ht
    have hlip : LipschitzWith ⟨Real.exp (K*t),(Real.exp_pos _).le⟩ (fun z => Φ z t) := by
      apply LipschitzWith.of_dist_le_mul
      intro z w
      simpa only [hΦ0,mul_comm] using lift_ode_dist f K hK (Φ z) (Φ w)
        (fun s _ => hΦd z s) (fun s _ => hΦd w s) t ht
    exact hlip.continuous

/-- The actual normalized vector field has a continuous forward flow on the
compact closure of physical states. Invariance is proved by source trajectories,
uniqueness and closure, not assumed as a new boundary-flow contract. -/
theorem normalized_closed_flow (p : Rates) (hp : PositiveRates p) (ru rv rj R : ℝ)
    (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj)
    (hR : p.recruitment/deathFloor p+1 ≤ R) :
    ∃ Φ : LiftState → ℝ → LiftState,
      (∀ z, Φ z 0 = z) ∧
      (∀ t, 0 ≤ t → Continuous (fun z => Φ z t)) ∧
      (∀ z ∈ physicalLiftClosure ru rv rj R, ∀ t, 0 ≤ t →
        Φ z t ∈ physicalLiftClosure ru rv rj R ∧
        HasDerivAt (Φ z) (normalizedField p ru rv rj (Φ z t)) t) ∧
      (∀ z s t, 0 ≤ s → 0 ≤ t → Φ z (s+t) = Φ (Φ z s) t) := by
  obtain ⟨f,K,Φ,hK,hfone,hΦ0,hΦd,hΦc⟩ := normalized_cutoff_flow p ru rv rj R
  have hphysical : ∀ t, 0 ≤ t → ∀ z ∈ physicalLiftSet ru rv rj R,
      Φ z t ∈ physicalLiftSet ru rv rj R := by
    intro t ht z hz
    obtain ⟨x,⟨hx,hN⟩,rfl⟩ := hz
    let xb : populationBox R := ⟨x,fun i => (hx i).le,hN⟩
    let X := boxFlow p hp R xb
    let Z : ℝ → LiftState := fun s => normalizedEmbedding ru rv rj (X s)
    have hXs := boxFlow_spec p hp R hR xb
    have hXp : ∀ s, 0 ≤ s → ∀ i, 0 < X s i := by
      intro s hs i
      exact boxFlow_coordinate_positive p hp R hR xb i (hx i) s hs
    have hZd : ∀ s, 0 ≤ s → HasDerivAt Z (f (Z s)) s := by
      intro s hs
      have hn := normalizedEmbedding_norm_le ru rv rj R (X s) hru hrv hrj (hXp s hs) (hXs.2.1 s hs).2
      rw [hfone _ hn]
      obtain ⟨hU,hV,hJ⟩ := positive_masses ru rv rj (X s) hru hrv hrj (hXp s hs)
      exact normalizedEmbedding_derivative p ru rv rj X s hru.ne' hrv.ne' hrj.ne'
        hU.ne' hV.ne' hJ.ne' (hXs.2.2 s hs)
    have hZ0 : Z 0 = normalizedEmbedding ru rv rj x := by
      dsimp [Z,X]
      rw [hXs.1]
    have hh := lift_ode_dist f K hK (Φ (normalizedEmbedding ru rv rj x)) Z
      (fun s _ => hΦd _ s) hZd t ht
    have heq : Φ (normalizedEmbedding ru rv rj x) t = Z t := by
      apply dist_le_zero.mp
      simpa only [hΦ0,hZ0,dist_self,zero_mul] using hh
    rw [heq]
    exact ⟨X t,⟨hXp t ht,(hXs.2.1 t ht).2⟩,rfl⟩
  have hclosure : ∀ t, 0 ≤ t → ∀ z ∈ physicalLiftClosure ru rv rj R,
      Φ z t ∈ physicalLiftClosure ru rv rj R := by
    intro t ht
    have hs : physicalLiftSet ru rv rj R ⊆ (fun z => Φ z t) ⁻¹' physicalLiftClosure ru rv rj R := by
      intro z hz
      exact subset_closure (hphysical t ht z hz)
    have hc : IsClosed ((fun z => Φ z t) ⁻¹' physicalLiftClosure ru rv rj R) :=
      isClosed_closure.preimage (hΦc t ht)
    exact closure_minimal hs hc
  refine ⟨Φ,hΦ0,hΦc,?_,?_⟩
  · intro z hz t ht
    have hzt := hclosure t ht z hz
    refine ⟨hzt,?_⟩
    have hn := physicalLiftClosure_norm_le ru rv rj R hru hrv hrj (Φ z t) hzt
    simpa only [hfone _ hn] using hΦd z t
  · intro z s t hs ht
    let X : ℝ → LiftState := fun τ => Φ z (s+τ)
    have hXd : ∀ τ, 0 ≤ τ → HasDerivAt X (f (X τ)) τ := by
      intro τ _
      simpa [X] using (hΦd z (s+τ)).scomp τ ((hasDerivAt_id τ).const_add s)
    have hh := lift_ode_dist f K hK X (Φ (Φ z s)) hXd (fun τ _ => hΦd _ τ) t ht
    apply dist_le_zero.mp
    simpa only [X,add_zero,hΦ0,dist_self,zero_mul] using hh

end OverlappingSiphonInvasion
