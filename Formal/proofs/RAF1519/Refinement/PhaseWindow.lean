import proofs.RAF1519.Refinement.PhaseWeightedAlgebra
import proofs.RAF1519.Refinement.GraphForcedLower

namespace RAF1519.Refinement
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 50000

/-- A pathwise phase transfer on one short window. Only the compensated
    primitive is differentiated; the observed phase path may jump. -/
theorem phase_window_lower {ι : Type*} [Fintype ι] (k : ι → ι → ℝ)
    (hk : ∀ i j, 0 ≤ k i j) (hsym : ∀ i j, k i j=k j i)
    (Δ ε S : ℝ) (hΔ : 0 ≤ Δ) (hε : 0 ≤ ε) (hdegree : ∀ i, (∑ j, k i j) ≤ Δ)
    (X F v : ℝ → ι → Fin 4 → ℝ)
    (hc : ∀ i p, ContinuousOn (fun t => F t i p) (Set.Icc 0 (1/28)))
    (hd : ∀ t ∈ Set.Ico 0 (1/28), ∀ i p,
      HasDerivWithinAt (fun u => F u i p) (v t i p) (Set.Ici t) t)
    (hX : ∀ t ∈ Set.Icc 0 (1/28), ∀ i p, 0 ≤ X t i p)
    (hn : ∀ t ∈ Set.Icc 0 (1/28), ∀ i p, |X t i p-F t i p| ≤ ε)
    (h0 : ∀ i, S ≤ phaseDot phaseWeight (X 0 i))
    (hv : ∀ t ∈ Set.Ico 0 (1/28), ∀ i p,
      (∑ q, phaseM p q*X t i q)+graphDiffusion k (fun j => X t j p) i ≤ v t i p) :
    ∀ i, S/8-8*(1+Δ)*ε ≤ X (1/28) i 0 := by
  let U := fun t i => phaseDot (fun p => phaseAdjoint (1/28) p t) (F t i)
  let W := fun t i => phaseDot (fun p => phaseAdjointDerivative (1/28) p t) (F t i)+
    phaseDot (fun p => phaseAdjoint (1/28) p t) (v t i)
  have hUc : ∀ i, ContinuousOn (fun t => U t i) (Set.Icc 0 (1/28)) := by
    intro i
    apply continuousOn_finsetSum
    intro p _
    exact (continuous_iff_continuousAt.mpr (fun t => (phaseAdjoint_derivative (1/28) p t).continuousAt)).continuousOn.mul (hc i p)
  have hUd : ∀ t ∈ Set.Ico 0 (1/28), ∀ i, HasDerivWithinAt (fun u => U u i) (W t i) (Set.Ici t) t := by
    intro t ht i
    have hh : HasDerivWithinAt (fun u => ∑ p : Fin 4, phaseAdjoint (1/28) p u*F u i p)
        (∑ p : Fin 4, (phaseAdjointDerivative (1/28) p t*F t i p+phaseAdjoint (1/28) p t*v t i p))
        (Set.Ici t) t :=
      HasDerivWithinAt.fun_sum (fun p _ =>
        (phaseAdjoint_derivative (1/28) p t).hasDerivWithinAt.mul (hd t ht i p))
    simpa only [U,W,phaseDot,Finset.sum_add_distrib] using hh
  have hU0 : ∀ i, S/8-(3/2)*ε ≤ U 0 i := by
    intro i
    have hb : phaseDot phaseWeight (X 0 i)/8 ≤
        phaseDot (fun p => phaseAdjoint (1/28) p 0) (X 0 i) := by
      unfold phaseDot
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro p _
      have hh := mul_le_mul_of_nonneg_right (phaseAdjoint_initial p) (hX 0 (by norm_num) i p)
      nlinarith
    have hnoise := phaseDot_noise (fun p => phaseAdjoint (1/28) p 0) (X 0 i) (F 0 i) ε
      (hn 0 (by norm_num) i)
    simp only [abs_of_nonneg (phaseAdjoint_nonnegative (1/28) 0 (by norm_num) _)] at hnoise
    have hnoise' := hnoise.trans (mul_le_mul_of_nonneg_right (phaseAdjoint_sum_bound (1/28) 0 (by norm_num)) hε)
    have hu := (abs_le.mp hnoise').2
    dsimp [U]
    linarith [h0 i]
  have hU := graph_forced_lower k hk hsym U W (1/28) (S/8-(3/2)*ε) ((132+3*Δ)*ε)
    hUc hUd hU0 (by
      intro t ht i
      exact phase_weighted_drift k hk Δ ε hΔ hε hdegree
        (fun p => phaseAdjoint (1/28) p t) (fun p => phaseAdjointDerivative (1/28) p t)
        (phaseAdjoint_nonnegative (1/28) t ht.2.le) (phaseAdjoint_sum_bound (1/28) t ht.2.le)
        (phaseAdjoint_derivative_sum_bound (1/28) t ht.2.le) (phaseAdjoint_residual (1/28) t)
        (X t) (F t) (v t) (hX t ⟨ht.1,ht.2.le⟩) (hn t ⟨ht.1,ht.2.le⟩) (hv t ht) i)
    (1/28) (by norm_num)
  intro i
  have hu := hU i
  have hend : U (1/28) i = F (1/28) i 0 := by
    dsimp [U,phaseDot]
    simp only [phaseAdjoint_terminal,ite_mul,one_mul,zero_mul]
    simp
  rw [hend] at hu
  have he := (abs_le.mp (hn (1/28) (by norm_num) i 0)).1
  nlinarith

end
end RAF1519.Refinement
