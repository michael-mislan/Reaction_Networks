import proofs.RAF1519.Reservoir.EnergyDynamics

namespace RAF1519.Reservoir
noncomputable section
open Set Filter Topology

/-- Local dissipation and a coercive smooth energy produce a genuine open
neighborhood of initial conditions with global convergent source trajectories. -/
theorem local_energy_attraction {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → (ι → ℝ))
    (V : (ι → ℝ) → ℝ) (DV : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ)
    (c : ι → ℝ) (good : Set (ι → ℝ)) (C κ : ℝ)
    (hC : 0 < C) (hκ : 0 < κ) (hf : ContDiff ℝ 1 f)
    (hV : ∀ x, HasFDerivAt V (DV x) x) (hVc : V c = 0)
    (hn : ∀ x, 0 ≤ V x) (hco : ∀ x i, (x i-c i)^2 ≤ C*V x)
    (hlocal : ∀ᶠ x in 𝓝 c, DV x (f x) ≤ -κ*V x ∧ x ∈ good) :
    ∃ ε > 0, ∀ x₀, dist x₀ c < ε →
      ∃ X : ℝ → ι → ℝ, X 0 = x₀ ∧
        (∀ t, 0 ≤ t → HasDerivAt X (f (X t)) t) ∧
        (∀ t, 0 ≤ t → X t ∈ good) ∧ Tendsto X atTop (𝓝 c) := by
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.1 hlocal
  let ρ := δ^2/(2*C)
  have hρ : 0 < ρ := div_pos (sq_pos_of_pos hδ) (by positivity)
  have hρid : C*ρ = δ^2/2 := by dsimp [ρ]; field_simp
  have hsmall (x : ι → ℝ) (hx : V x ≤ ρ) : dist x c < δ := by
    rw [dist_eq_norm]
    apply (pi_norm_lt_iff hδ).2
    intro i
    have h := (hco x i).trans (mul_le_mul_of_nonneg_left hx hC.le)
    rw [hρid] at h
    simp only [Pi.sub_apply,Real.norm_eq_abs,abs_lt]
    constructor <;> nlinarith [sq_nonneg (x i-c i-δ),sq_nonneg (x i-c i+δ)]
  let R := ‖c‖+δ+1
  have hR : 0 < R := by dsimp [R]; linarith [norm_nonneg c]
  have hb (x : ι → ℝ) (hx : V x ≤ ρ) : ‖x‖ ≤ R := by
    have h := hsmall x hx
    have htri : ‖x‖ ≤ ‖c‖+δ := norm_le_norm_add_const_of_dist_le h.le
    dsimp [R]
    linarith
  have hd (x : ι → ℝ) (hx : V x ≤ ρ) : DV x (f x) ≤ -κ*V x :=
    (hball (hsmall x hx)).1
  obtain ⟨ε,hε,hεV⟩ := Metric.continuousAt_iff.1 (hV c).continuousAt ρ hρ
  refine ⟨ε,hε,?_⟩
  intro x₀ hx₀
  have h0 : V x₀ ≤ ρ := by
    have h := hεV hx₀
    rw [hVc,Real.dist_eq,sub_zero] at h
    exact (le_abs_self _).trans h.le
  obtain ⟨X,hX0,hXd,hXE,hXlim⟩ := energy_sublevel_solution f V DV c x₀ R C ρ κ
    hR hC hρ hκ hf hV hn hco hb hd h0
  exact ⟨X,hX0,hXd,(fun t ht => (hball (hsmall (X t) (hXE t ht).1)).2),hXlim⟩

end
end RAF1519.Reservoir
