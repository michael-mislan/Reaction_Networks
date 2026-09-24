import proofs.OverlappingSiphonInvasion.GrowthExtension

noncomputable section
namespace OverlappingSiphonInvasion

/-- Continuous accumulated growth along the actual compact source lift.
Additivity is derived from the ODE, not supplied as an abstract cocycle premise. -/
theorem normalized_growth_cocycle (p : Rates) (hp : PositiveRates p) (ru rv rj R : ℝ)
    (k : ℕ) (hru : 0 < ru) (hrv : 0 < rv) (hrj : 0 < rj)
    (hR : p.recruitment/deathFloor p+1 ≤ R) :
    ∃ Φ : LiftState → ℝ → LiftState, ∃ A : LiftState → ℝ → ℝ,
      (∀ z, Φ z 0 = z) ∧ (∀ z, A z 0 = 0) ∧
      (∀ t, 0 ≤ t → Continuous (fun z => Φ z t) ∧ Continuous (fun z => A z t)) ∧
      (∀ z ∈ physicalLiftClosure ru rv rj R, ∀ t, 0 ≤ t →
        Φ z t ∈ physicalLiftClosure ru rv rj R ∧
        HasDerivAt (Φ z) (normalizedField p ru rv rj (Φ z t)) t ∧
        HasDerivAt (A z) (normalGrowth p ru rv rj k (Φ z t)) t) ∧
      (∀ z s t, 0 ≤ s → 0 ≤ t →
        Φ z (s+t) = Φ (Φ z s) t ∧ A z (s+t) = A z s+A (Φ z s) t) := by
  obtain ⟨H,K,Ψ,hK,hone,hΨ0,hΨd,hΨc⟩ := growth_extension p ru rv rj R k
  obtain ⟨φ,hφ0,_hφc,hφd,_hφadd⟩ := normalized_closed_flow p hp ru rv rj R hru hrv hrj hR
  let f : LiftState → LiftState := fun z => (H z).1
  have hf : LipschitzWith K f := by simpa using LipschitzWith.prod_fst.comp hK
  have hphysical : ∀ z ∈ physicalLiftClosure ru rv rj R, ∀ t, 0 ≤ t →
      (Ψ (z,0) t).1 = φ z t := by
    intro z hz t ht
    have hdφ : ∀ s, 0 ≤ s → HasDerivAt (φ z) (f (φ z s)) s := by
      intro s hs
      have hh := hφd z hz s hs
      have hn := physicalLiftClosure_norm_le ru rv rj R hru hrv hrj (φ z s) hh.1
      dsimp [f]
      rw [hone _ hn]
      exact hh.2
    have hh := globally_lipschitz_ode_distance f K hf (fun s => (Ψ (z,0) s).1) (φ z)
      (fun s _ => (hΨd (z,0) s).fst) hdφ t ht
    apply dist_le_zero.mp
    simpa only [hΨ0,hφ0,dist_self,zero_mul] using hh
  let Φ : LiftState → ℝ → LiftState := fun z t => (Ψ (z,0) t).1
  let A : LiftState → ℝ → ℝ := fun z t => (Ψ (z,0) t).2
  have hF : LipschitzWith K (fun w : GrowthState => H w.1) := by
    simpa using hK.comp LipschitzWith.prod_fst
  refine ⟨Φ,A,?_,?_,?_,?_,?_⟩
  · intro z
    simp only [Φ,hΨ0]
  · intro z
    simp only [A,hΨ0]
  · intro t ht
    have hh : Continuous (fun z : LiftState => Ψ (z,0) t) :=
      (hΨc t ht).comp (continuous_id.prodMk continuous_const)
    exact ⟨hh.fst,hh.snd⟩
  · intro z hz t ht
    have hzt : Φ z t ∈ physicalLiftClosure ru rv rj R := by
      rw [show Φ z t = φ z t from hphysical z hz t ht]
      exact (hφd z hz t ht).1
    have hn := physicalLiftClosure_norm_le ru rv rj R hru hrv hrj (Φ z t) hzt
    have hh := hΨd (z,0) t
    rw [hone _ hn] at hh
    exact ⟨hzt,hh.fst,hh.snd⟩
  · intro z s t _hs ht
    let Y : ℝ → GrowthState := fun τ =>
      ((Ψ (z,0) (s+τ)).1,(Ψ (z,0) (s+τ)).2-(Ψ (z,0) s).2)
    have hdY : ∀ τ, 0 ≤ τ → HasDerivAt Y (H (Y τ).1) τ := by
      intro τ _
      have hh : HasDerivAt (fun u => Ψ (z,0) (s+u)) (H (Ψ (z,0) (s+τ)).1) τ := by
        simpa using (hΨd (z,0) (s+τ)).scomp τ ((hasDerivAt_id τ).const_add s)
      have hh1 : HasDerivAt (fun u => (Ψ (z,0) (s+u)).1)
          (H (Ψ (z,0) (s+τ)).1).1 τ := hh.fst
      have hh2 : HasDerivAt (fun u => (Ψ (z,0) (s+u)).2)
          (H (Ψ (z,0) (s+τ)).1).2 τ := hh.snd
      exact hh1.prodMk (hh2.sub_const ((Ψ (z,0) s).2))
    have hh := globally_lipschitz_ode_distance (fun w : GrowthState => H w.1) K hF
      Y (Ψ ((Ψ (z,0) s).1,0)) hdY (fun τ _ => hΨd _ τ) t ht
    have heq : Y t = Ψ ((Ψ (z,0) s).1,0) t := by
      apply dist_le_zero.mp
      simpa only [Y,add_zero,sub_self,hΨ0,dist_self,zero_mul] using hh
    constructor
    · simpa only [Y,Φ] using congrArg Prod.fst heq
    · have hh' := congrArg Prod.snd heq
      change A z (s+t)-A z s = A (Φ z s) t at hh'
      linarith

end OverlappingSiphonInvasion
