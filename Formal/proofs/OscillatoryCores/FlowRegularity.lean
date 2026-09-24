import proofs.Bressan.Flow.SmoothODE
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace OscillatoryCores

open Set Filter
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem variational_norm_bound (A J : ℝ → E →L[ℝ] E) (T K : ℝ≥0)
    (hJ : ∀ t ∈ Icc (0 : ℝ) T,
      HasDerivWithinAt J ((A t).comp (J t)) (Icc (0 : ℝ) T) t)
    (h0 : J 0 = ContinuousLinearMap.id ℝ E)
    (hA : ∀ t ∈ Icc (0 : ℝ) T, ‖A t‖ ≤ K) :
    ∀ t ∈ Icc (0 : ℝ) T, ‖J t‖ ≤ Real.exp ((K : ℝ)*t) := by
  have hc : ContinuousOn J (Icc (0 : ℝ) T) := HasDerivWithinAt.continuousOn hJ
  have hd : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt J ((A t).comp (J t)) (Ici t) t := by
    intro t ht
    exact (hJ t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
  have hz : ‖J 0‖ ≤ (1 : ℝ) := by rw [h0]; exact ContinuousLinearMap.norm_id_le
  have hb : ∀ t ∈ Ico (0 : ℝ) T,
      ‖(A t).comp (J t)‖ ≤ (K : ℝ)*‖J t‖ + 0 := by
    intro t ht
    simpa using (ContinuousLinearMap.opNorm_comp_le (A t) (J t)).trans
      (mul_le_mul_of_nonneg_right (hA t ⟨ht.1, ht.2.le⟩) (norm_nonneg _))
  intro t ht
  simpa [gronwallBound_ε0] using
    norm_le_gronwallBound_of_norm_deriv_right_le hc hd hz hb t ht

private theorem gronwall_zero_scale (K a t : ℝ) :
    gronwallBound 0 K a t = a * gronwallBound 0 K 1 t := by
  by_cases hK : K = 0
  · subst K; simp [gronwallBound_K0]
  · simp only [gronwallBound_of_K_ne_0 hK, zero_mul, zero_add]
    ring

/-- Continuity of the full operator-valued derivative, derived from the
variational ODE and spatial Lipschitz bounds. -/
theorem variational_endpoint_continuous
    (v : ℝ → E → E) (Dv : ℝ → E → E →L[ℝ] E)
    (X : E → ℝ → E) (J : E → ℝ → E →L[ℝ] E) (T K L : ℝ≥0)
    (hv : ∀ t, LipschitzWith K (v t))
    (hvD : ∀ t z, HasFDerivAt (v t) (Dv t z) z)
    (hDv : ∀ t, LipschitzWith L (Dv t))
    (hX : ∀ x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (X x) (v t (X x t)) (Icc (0 : ℝ) T) t)
    (hzero : ∀ x, X x 0 = x)
    (hJ : ∀ x t, t ∈ Icc (0 : ℝ) T →
      HasDerivWithinAt (J x) ((Dv t (X x t)).comp (J x t)) (Icc (0 : ℝ) T) t)
    (hJzero : ∀ x, J x 0 = ContinuousLinearMap.id ℝ E)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) T) : Continuous (fun x => J x u) := by
  have hA (x t) : ‖Dv t (X x t)‖ ≤ K := by
    rw [← (hvD t (X x t)).fderiv]
    exact norm_fderiv_le_of_lipschitz ℝ (hv t)
  have hJn (x t) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖J x t‖ ≤ Real.exp ((K : ℝ)*t) :=
    variational_norm_bound (fun t => Dv t (X x t)) (J x) T K
      (hJ x) (hJzero x) (fun t _ => hA x t) t ht
  let C : ℝ := (L : ℝ)*Real.exp ((K : ℝ)*T)^2
  have hbound (x y : E) :
      ‖J y u - J x u‖ ≤ C * ‖y-x‖ * gronwallBound 0 K 1 u := by
    let R : ℝ → E →L[ℝ] E := fun t => J y t - J x t
    let R' : ℝ → E →L[ℝ] E := fun t =>
      (Dv t (X y t)).comp (J y t) - (Dv t (X x t)).comp (J x t)
    have hc : ContinuousOn R (Icc (0 : ℝ) T) :=
      HasDerivWithinAt.continuousOn (fun t ht => (hJ y t ht).sub (hJ x t ht))
    have hd : ∀ t ∈ Ico (0 : ℝ) T, HasDerivWithinAt R (R' t) (Ici t) t := by
      intro t ht
      exact ((hJ y t ⟨ht.1, ht.2.le⟩).sub (hJ x t ⟨ht.1, ht.2.le⟩)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)
    have hz : ‖R 0‖ ≤ (0 : ℝ) := by simp [R, hJzero]
    have hb : ∀ t ∈ Ico (0 : ℝ) T, ‖R' t‖ ≤ (K : ℝ)*‖R t‖ + C*‖y-x‖ := by
      intro t ht
      have ht' : t ∈ Icc (0 : ℝ) T := ⟨ht.1,ht.2.le⟩
      have hs := Bressan.odeTrajectoryOn_Icc_norm_sub_le_exp v X T K hv hX hzero x y t ht'
      have he : Real.exp ((K : ℝ)*t) ≤ Real.exp ((K : ℝ)*T) := by gcongr; exact ht.2.le
      have hD : ‖Dv t (X y t) - Dv t (X x t)‖ ≤
          (L : ℝ)*(‖y-x‖*Real.exp ((K : ℝ)*T)) := by
        calc
          _ ≤ (L : ℝ)*‖X y t-X x t‖ := (hDv t).norm_sub_le _ _
          _ ≤ (L : ℝ)*(‖y-x‖*Real.exp ((K : ℝ)*T)) := by
            gcongr
            exact (by simpa using hs : ‖X y t-X x t‖ ≤ ‖y-x‖*Real.exp ((K : ℝ)*t))
              |>.trans (mul_le_mul_of_nonneg_left he (norm_nonneg _))
      have hsplit : R' t = (Dv t (X y t)).comp (R t) +
          (Dv t (X y t)-Dv t (X x t)).comp (J x t) := by
        simp only [R', R, ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
        abel
      rw [hsplit]
      calc
        _ ≤ ‖(Dv t (X y t)).comp (R t)‖ +
            ‖(Dv t (X y t)-Dv t (X x t)).comp (J x t)‖ := norm_add_le _ _
        _ ≤ (K : ℝ)*‖R t‖ + ((L : ℝ)*(‖y-x‖*Real.exp ((K : ℝ)*T)))*
            Real.exp ((K : ℝ)*T) := by
          apply add_le_add
          · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul_of_nonneg_right (hA y t) (norm_nonneg _))
          · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul hD ((hJn x t ht').trans he) (norm_nonneg _) (by positivity))
        _ = (K : ℝ)*‖R t‖ + C*‖y-x‖ := by dsimp [C]; ring
    have h := norm_le_gronwallBound_of_norm_deriv_right_le hc hd hz hb u hu
    rw [gronwall_zero_scale] at h
    simpa only [R, sub_zero] using h
  apply continuous_iff_continuousAt.mpr
  intro x
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hlim : Tendsto (fun y : E => C*‖y-x‖*gronwallBound 0 K 1 u) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : E => C*‖y-x‖*gronwallBound 0 K 1 u) := by fun_prop
    simpa using hc.tendsto x
  exact squeeze_zero (fun _ => dist_nonneg) (fun y => by simpa [dist_eq_norm] using hbound x y) hlim

end OscillatoryCores
