import proofs.CoreCouplingCAC.GlobalExistence
import proofs.CoreCouplingCAC.EnergyBarrier

namespace RAF1519.Reservoir
noncomputable section
open Set Filter Topology

/-- A local energy estimate constructs a global actual solution by removing
the auxiliary cutoff on its invariant sublevel. Its source-specific energy
and dissipation hypotheses must be proved separately. -/
theorem energy_sublevel_solution {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → ℝ) → (ι → ℝ))
    (V : (ι → ℝ) → ℝ) (DV : (ι → ℝ) → (ι → ℝ) →L[ℝ] ℝ)
    (c x₀ : ι → ℝ) (R C ρ κ : ℝ)
    (hR : 0 < R) (hC : 0 < C) (hρ : 0 < ρ) (hκ : 0 < κ)
    (hf : ContDiff ℝ 1 f) (hV : ∀ x, HasFDerivAt V (DV x) x)
    (hn : ∀ x, 0 ≤ V x)
    (hco : ∀ x i, (x i-c i)^2 ≤ C*V x)
    (hbounded : ∀ x, V x ≤ ρ → ‖x‖ ≤ R)
    (hdec : ∀ x, V x ≤ ρ → DV x (f x) ≤ -κ*V x)
    (h0 : V x₀ ≤ ρ) :
    ∃ X : ℝ → ι → ℝ, X 0 = x₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt X (f (X t)) t) ∧
      (∀ t, 0 ≤ t → V (X t) ≤ ρ ∧ V (X t) ≤ V x₀*Real.exp (-κ*t)) ∧
      Tendsto X atTop (𝓝 c) := by
  let b : ContDiffBump (0 : ι → ℝ) := ⟨R,2*R,hR,by linarith⟩
  let g := fun x => b x • f x
  have hs : HasCompactSupport g := b.hasCompactSupport.smul_right
  have hg : ContDiff ℝ 1 g := b.contDiff.smul hf
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hg (by norm_num)
  obtain ⟨L,hL⟩ := hs.exists_bound_of_continuous hg.continuous
  obtain ⟨X,hX0,hXd⟩ := CoreCouplingCAC.bounded_lipschitz_global_solution g K
    ⟨max L 0,le_max_right _ _⟩ hK (fun x => (hL x).trans (le_max_left _ _)) x₀
  have hb1 (x : ι → ℝ) (hx : V x ≤ ρ) : b x = 1 :=
    b.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right]
      using (hbounded x hx))
  have hE (t : ℝ) : HasDerivAt (fun t => V (X t)) (DV (X t) (g (X t))) t :=
    (hV (X t)).comp_hasDerivAt t (hXd t)
  have hkeep (t : ℝ) (ht : 0 ≤ t) :
      V (X t) ≤ ρ ∧ V (X t) ≤ V x₀*Real.exp (-κ*t) := by
    have hh := CoreCouplingCAC.local_energy_barrier (fun t => V (X t))
      (fun t => DV (X t) (g (X t))) t ρ κ hρ hκ
      (fun s _ => (hE s).continuousAt.continuousWithinAt)
      (fun s _ => (hE s).hasDerivWithinAt) (by simpa only [hX0] using h0)
      (fun s _ hs => by simpa only [g,hb1 (X s) hs,one_smul] using hdec (X s) hs)
    simpa only [hX0] using hh t ⟨ht,le_rfl⟩
  refine ⟨X,hX0,?_,hkeep,?_⟩
  · intro t ht
    simpa only [g,hb1 (X t) (hkeep t ht).1,one_smul] using hXd t
  · have hlim : Tendsto (fun t => V (X t)) atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall (fun t => hn (X t)))
        (eventually_ge_atTop 0 |>.mono (fun t ht => (hkeep t ht).2))
      simpa using (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hκ))).const_mul (V x₀)
    have hsqrt : Tendsto (fun t => Real.sqrt (C*V (X t))) atTop (𝓝 0) := by
      simpa only [Function.comp_apply,mul_zero,Real.sqrt_zero] using
        Real.continuous_sqrt.continuousAt.tendsto.comp (hlim.const_mul C)
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_iff_dist_tendsto_zero.2
    simp only [Real.dist_eq]
    apply squeeze_zero (fun _ => abs_nonneg _) ?_ hsqrt
    intro t
    apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg hC.le (hn (X t)))).2
    simpa only [sq_abs] using hco (X t) i

end
end RAF1519.Reservoir
