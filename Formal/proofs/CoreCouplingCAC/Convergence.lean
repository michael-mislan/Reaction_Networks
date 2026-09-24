import proofs.CoreCouplingCAC.ConcreteSelection
import proofs.CoreCouplingCAC.SourceAdapter

open Filter Topology

namespace CoreCouplingCAC

theorem energy_decay_converges (L R c : Fin 4 → ℝ) (x : ℝ → Fin 4 → ℝ) (M : ℝ)
    (hw : ∀ i, (1/4:ℝ) ≤ L i/R i)
    (hb : ∀ t, 0 ≤ t → energy L R c (x t) ≤ M*Real.exp (-(1/100:ℝ)*t)) :
    Tendsto x atTop (𝓝 c) := by
  have hn : ∀ t, 0 ≤ energy L R c (x t) := by
    intro t
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (by linarith [hw i]) (sq_nonneg _))
  have he : Tendsto (fun t => energy L R c (x t)) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall hn) (eventually_ge_atTop 0 |>.mono (fun t ht => hb t ht))
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1/100:ℝ) < 0))).const_mul M
  have hs : Tendsto (fun t => Real.sqrt (4*energy L R c (x t))) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero,Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp (he.const_mul 4)
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_iff_dist_tendsto_zero.2
  simp only [Real.dist_eq]
  apply squeeze_zero (fun _ => abs_nonneg _) ?_ hs
  intro t
  apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg (by norm_num) (hn t))).2
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin 4)),
      0 ≤ (L j/R j)*(x t j-c j)^2 := by
    intro j _
    exact mul_nonneg (by linarith [hw j]) (sq_nonneg _)
  have hterm : (L i/R i)*(x t i-c i)^2 ≤ energy L R c (x t) :=
    Finset.single_le_sum hnonneg (Finset.mem_univ i)
  have hh := mul_nonneg (sub_nonneg.mpr (hw i)) (sq_nonneg (x t i-c i))
  rw [sq_abs]
  nlinarith

theorem transformed_derivative_source (p : Rates) (X : ℝ → State) (t : ℝ)
    (hd : HasDerivAt (fun s => transform (X s)) (dynamics p (transform (X t))) t) :
    HasDerivAt (fun s => coordinates (X s)) (sourceDerivative p (X t)) t := by
  have h := hasDerivAt_pi.1 hd
  rw [dynamics_source] at h
  have hA := (h 0).add (h 1)
  have hB := (h 1).neg
  have hz := h 2
  have hH := h 3
  simp [transform] at hA hB hz hH
  rw [literal_source_adapter]
  apply hasDerivAt_pi.2
  intro i
  fin_cases i
  · convert hA using 1
    funext s
    simp [coordinates]
  · convert hB using 1
    funext s
    simp [coordinates]
  · simpa [coordinates] using hz
  · simpa [coordinates] using hH

theorem transformed_convergence_source (X : ℝ → State) (c : State)
    (h : Tendsto (fun t => transform (X t)) atTop (𝓝 (transform c))) :
    Tendsto (fun t => coordinates (X t)) atTop (𝓝 (coordinates c)) := by
  have hh := tendsto_pi_nhds.1 h
  apply tendsto_pi_nhds.2
  intro i
  fin_cases i
  · simpa [coordinates,transform] using (hh 0).add (hh 1)
  · simpa [coordinates,transform] using (hh 1).neg
  · simpa [coordinates,transform] using hh 2
  · simpa [coordinates,transform] using hh 3

end CoreCouplingCAC
