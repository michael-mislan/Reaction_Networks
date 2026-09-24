import proofs.ProductiveMemory.ExtractionEnergyDerivative
import proofs.ProductiveMemory.ExtractionWell

namespace ProductiveMemory
open FiniteCopy Set Filter Topology
noncomputable section
set_option Elab.async false

theorem extraction_contDiff (rho : ℝ) : ContDiff ℝ 1 (extractDrift rho 0) := by
  apply contDiff_pi.2
  intro i
  fin_cases i <;> norm_num [extractDrift,drift_formula,Matrix.cons_val_two,Matrix.cons_val_three] <;> fun_prop

theorem extraction_global_extension (rho : ℝ) :
    ∃ f : Point → Point, (∀ x, ‖x‖ ≤ 100 → f x=extractDrift rho 0 x) ∧
      ∀ x₀, ∃ x : ℝ → Point, x 0=x₀ ∧ ∀ t, HasDerivAt x (f (x t)) t := by
  let b : ContDiffBump (0:Point) := ⟨100,200,by norm_num,by norm_num⟩
  let f : Point → Point := fun x => b x • extractDrift rho 0 x
  have hs : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hd : ContDiff ℝ 1 f := b.contDiff.smul (extraction_contDiff rho)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hd (by norm_num)
  obtain ⟨C,hC⟩ := hs.exists_bound_of_continuous hd.continuous
  refine ⟨f,?_,?_⟩
  · intro x hx
    have hb : b x=1 := b.one_of_mem_closedBall (by simpa [b,dist_zero_right] using hx)
    simp [f,hb]
  · intro x₀
    exact CoreCouplingCAC.bounded_lipschitz_global_solution f K ⟨max C 0,le_max_right _ _⟩ hK
      (fun x => (hC x).trans (le_max_left _ _)) x₀

theorem extraction_energy_attraction (rho : ℝ) (c : Point) (E : Point → ℝ) (P : Point → Point → ℝ)
    (hc : ∀ i, |c i| ≤ 34)
    (hlo : ∀ y, (1/200:ℝ)*normSq y ≤ E y) (hup : ∀ y, E y ≤ 60*normSq y)
    (hd : ∀ (x : ℝ → Point) v t, HasDerivAt x v t →
      HasDerivAt (fun s => E (fun i => x s i-c i)) (2*P (fun i => x t i-c i) v) t)
    (hdec : ∀ y, (∀ i, |y i| ≤ 1/400) →
      2*P y (extractDrift rho 0 (fun i => c i+y i)) ≤ -(59/100)*normSq y)
    (x₀ : Point) (h₀ : E (fun i => x₀ i-c i) ≤ outerLevel) :
    ∃ x : ℝ → Point, x 0=x₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt x (extractDrift rho 0 (x t)) t ∧
        E (fun i => x t i-c i) ≤ outerLevel ∧
        E (fun i => x t i-c i) ≤ E (fun i => x₀ i-c i)*Real.exp (-(1/1000:ℝ)*t)) ∧
      Tendsto x atTop (𝓝 c) := by
  obtain ⟨f,hf,hglobal⟩ := extraction_global_extension rho
  obtain ⟨x,hx₀,hx⟩ := hglobal x₀
  let F : ℝ → ℝ := fun t => E (fun i => x t i-c i)
  let V : ℝ → ℝ := fun t => 2*P (fun i => x t i-c i) (f (x t))
  have hFd (t : ℝ) : HasDerivAt F (V t) t := hd x (f (x t)) t (hx t)
  have hnorm (t : ℝ) (h : F t ≤ outerLevel) : ‖x t‖ ≤ 100 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ)≤100)).mpr
    intro i
    have hi := energy_controls_coordinates E hlo c (x t) h i
    have hh := abs_add_le (x t i-c i) (c i)
    rw [sub_add_cancel] at hh
    simpa only [Real.norm_eq_abs] using hh.trans (by linarith only [hi,hc i])
  have hb (t : ℝ) (ht : 0 ≤ t) : F t ≤ outerLevel ∧
      F t ≤ F 0*Real.exp (-(1/1000:ℝ)*t) := by
    apply CoreCouplingCAC.local_energy_barrier F V t outerLevel (1/1000)
      (by norm_num [outerLevel]) (by norm_num)
      (fun s _ => (hFd s).continuousAt.continuousWithinAt)
      (fun s _ => (hFd s).hasDerivWithinAt) (by simpa only [F,hx₀] using h₀) ?_ t ⟨ht,le_rfl⟩
    intro s _ hs
    have hp := hdec (fun i => x s i-c i) (energy_controls_coordinates E hlo c (x s) hs)
    have he := hup (fun i => x s i-c i)
    have hn := normSq_nonneg (fun i => x s i-c i)
    have hi : (fun i => c i+(x s i-c i))=x s := by ext i; ring
    rw [hi] at hp
    dsimp only [V,F]
    rw [hf (x s) (hnorm s hs)]
    linarith only [hp,he,hn]
  refine ⟨x,hx₀,?_,?_⟩
  · intro t ht
    refine ⟨?_,(hb t ht).1,?_⟩
    · rw [← hf (x t) (hnorm t (hb t ht).1)]
      exact hx t
    · simpa only [F,hx₀] using (hb t ht).2
  · have hn (t : ℝ) : 0 ≤ F t :=
      (mul_nonneg (by norm_num) (normSq_nonneg _)).trans (hlo _)
    have he : Tendsto F atTop (𝓝 0) := by
      apply squeeze_zero' (Eventually.of_forall hn) (eventually_ge_atTop 0 |>.mono (fun t ht => (hb t ht).2))
      simpa using (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg (by norm_num : -(1/1000:ℝ)<0))).const_mul (F 0)
    have hs : Tendsto (fun t => Real.sqrt (200*F t)) atTop (𝓝 0) := by
      simpa only [Function.comp_apply,mul_zero,Real.sqrt_zero] using
        Real.continuous_sqrt.continuousAt.tendsto.comp (he.const_mul 200)
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_iff_dist_tendsto_zero.2
    simp only [Real.dist_eq]
    apply squeeze_zero (fun _ => abs_nonneg _) ?_ hs
    intro t
    apply (Real.le_sqrt (abs_nonneg _) (mul_nonneg (by norm_num) (hn t))).2
    rw [sq_abs]
    have hcoord := coordinate_sq_le_normSq (fun j => x t j-c j) i
    have hel := hlo (fun j => x t j-c j)
    change (x t i-c i)^2 ≤ _ at hcoord
    change _ ≤ 200*E (fun j => x t j-c j)
    linarith only [hcoord,hel]

end
end ProductiveMemory
