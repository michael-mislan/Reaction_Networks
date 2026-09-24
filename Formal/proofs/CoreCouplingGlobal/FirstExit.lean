import proofs.CoreCouplingGlobal.LocalConeExit

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

/-- A continuous path crossing a level has a first positive hitting time,
and remains strictly below that level before the hit. -/
theorem first_level_hit (f : ℝ → ℝ) (T r : ℝ) (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc 0 T)) (h0 : f 0 < r) (hTop : r ≤ f T) :
    ∃ τ : ℝ, τ ∈ Ioc 0 T ∧ f τ = r ∧ ∀ t ∈ Ico 0 τ, f t < r := by
  let S := Icc 0 T ∩ f ⁻¹' {r}
  have hclosed : IsClosed S := hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed
    (by intro t ht; exact ht.1)
  obtain ⟨s,hs,hfs⟩ := intermediate_value_Icc hT hf ⟨h0.le,hTop⟩
  have hnonempty : S.Nonempty := ⟨s,hs,by simpa using hfs⟩
  obtain ⟨τ,hτ⟩ := hcompact.exists_isLeast hnonempty
  have hτ0 : 0 ≤ τ := hτ.1.1.1
  have hτT : τ ≤ T := hτ.1.1.2
  have hτr : f τ = r := hτ.1.2
  have hτpos : 0 < τ := by
    by_contra hn
    have heq : τ = 0 := by linarith
    rw [heq] at hτr
    linarith
  refine ⟨τ,⟨hτpos,hτT⟩,hτr,?_⟩
  intro t ht
  by_contra hn
  have hrt : r ≤ f t := le_of_not_gt hn
  have hct : ContinuousOn f (Icc 0 t) := hf.mono
    (by intro u hu; exact ⟨hu.1,le_trans hu.2 (le_trans ht.2.le hτT)⟩)
  obtain ⟨u,hu,hfu⟩ := intermediate_value_Icc ht.1 hct ⟨h0.le,hrt⟩
  have huS : u ∈ S := ⟨⟨hu.1,le_trans hu.2 (le_trans ht.2.le hτT)⟩,by simpa using hfu⟩
  have hminimal := hτ.2 huS
  linarith [hu.2,ht.2]

theorem negative_through_interval (q dq : ℝ → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (hd : ∀ t ∈ Icc 0 T, HasDerivAt q (dq t) t)
    (hdec : ∀ t ∈ Icc 0 T, dq t ≤ 0) (h0 : q 0 < 0) :
    ∀ t ∈ Icc 0 T, q t ≤ q 0 ∧ q t < 0 := by
  have hmono : AntitoneOn q (Icc 0 T) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 T)
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      exact hdec t (interior_subset ht)
  intro t ht
  have hle := hmono (show (0:ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩) ht ht.1
  exact ⟨hle,hle.trans_lt h0⟩

theorem saddleCoordinates_continuousOn (e : ℝ) (X : ℝ → State)
    (hX : IsPositiveTrajectory e X) : ContinuousOn (fun t => saddleCoordinates e (X t)) (Ici 0) := by
  have hA : ContinuousOn (fun t => (X t).A) (Ici 0) :=
    fun t ht => (hX.dA t ht).continuousAt.continuousWithinAt
  have hB : ContinuousOn (fun t => (X t).B) (Ici 0) :=
    fun t ht => (hX.dB t ht).continuousAt.continuousWithinAt
  have hz : ContinuousOn (fun t => (X t).z) (Ici 0) :=
    fun t ht => (hX.dz t ht).continuousAt.continuousWithinAt
  have hH : ContinuousOn (fun t => (X t).H) (Ici 0) :=
    fun t ht => (hX.dH t ht).continuousAt.continuousWithinAt
  have hh : ContinuousOn (fun t => responseTotal e (X t).B) (Ici 0) :=
    hB.add ((responseA_continuous e).comp_continuousOn hB)
  apply continuousOn_pi.mpr
  intro i
  fin_cases i
  · exact hB
  · exact hz
  · exact hH
  · exact (hA.add hB).sub hh

noncomputable def pairConeValue (e z α : ℝ) (X Y : ℝ → State) (t : ℝ) : ℝ :=
  perturbedSaddleQuadratic e z α (saddleCoordinates e (X t)-saddleCoordinates e (Y t))

/-- First exit at a smaller radius retains the negative quadratic value
through the hitting time for two literal positive trajectories. -/
theorem middle_first_exit_at_radius (e z H : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ α d : ℝ, 0 < α ∧ 0 < d ∧
      perturbedSaddleQuadratic e z α
        ![-(60/(z+2))/(z+2),1,(16+4*z)/(20001/10000),0] < 0 ∧
      ∀ r : ℝ, 0 < r → r < d → ∀ X Y : ℝ → State, IsPositiveTrajectory e X → IsPositiveTrajectory e Y →
      (∀ t : ℝ, 0 ≤ t → dist (saddleCoordinates e (X t)) ![60/(z+2),z,H,0] < r/2) →
      dist (saddleCoordinates e (Y 0)) ![60/(z+2),z,H,0] < r →
      pairConeValue e z α X Y 0 < 0 →
      ∃ τ : ℝ, 0 < τ ∧ dist (saddleCoordinates e (Y τ)) ![60/(z+2),z,H,0] = r ∧
        (∀ t ∈ Ico 0 τ, dist (saddleCoordinates e (Y t)) ![60/(z+2),z,H,0] < r) ∧
        (∀ t ∈ Icc 0 τ, pairConeValue e z α X Y t ≤ pairConeValue e z α X Y 0 ∧
          pairConeValue e z α X Y t < 0) ∧
        (∀ t ∈ Icc 0 τ, (X t).B ≠ (Y t).B) := by
  obtain ⟨α,η,δ,hα,hη,hδ,htangent,hpair,hexit⟩ := middle_actual_exit_certificate e z H he hu hz
  refine ⟨α,min δ 1,hα,lt_min hδ (by norm_num),htangent,?_⟩
  intro r hr hrd X Y hX hY hstay hY0 hstart
  have hrδ : r < δ := hrd.trans_le (min_le_left _ _)
  have hr1 : r < 1 := hrd.trans_le (min_le_right _ _)
  let p : SaddleVector := ![60/(z+2),z,H,0]
  obtain ⟨T,hT,hcases⟩ := hexit X Y hX hY hstart
  have hTY : r ≤ dist (saddleCoordinates e (Y T)) p := by
    rcases hcases with hbad | hgood
    · have hh := hstay T hT
      linarith
    · exact hrδ.le.trans hgood
  have hf : ContinuousOn (fun t => dist (saddleCoordinates e (Y t)) p) (Icc 0 T) := by
    simpa only [dist_eq_norm] using
      (((saddleCoordinates_continuousOn e Y hY).sub (continuousOn_const (c := p))).norm.mono
        (show Icc (0:ℝ) T ⊆ Ici 0 from fun _ ht => ht.1))
  obtain ⟨τ,hτ,hlevel,hbefore⟩ := first_level_hit _ T r hT hf hY0 hTY
  have hYclosed : ∀ t ∈ Icc 0 τ, dist (saddleCoordinates e (Y t)) p ≤ r := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · exact (hbefore t ⟨ht.1,hlt⟩).le
    · rw [heq,hlevel]
  let v := fun t => saddleCoordinates e (X t)-saddleCoordinates e (Y t)
  let dq := fun t => saddlePairing
    (perturbedGradient (saddleGradient e z).toContinuousLinearMap α (v t))
    (responseCoordinateField e (saddleCoordinates e (X t))-
      responseCoordinateField e (saddleCoordinates e (Y t)))
  have hd : ∀ t ∈ Icc 0 τ, HasDerivAt (pairConeValue e z α X Y) (dq t) t := by
    intro t ht
    have hBX := middle_unit_neighborhood_B_bounds z H hz (saddleCoordinates e (X t))
      (show dist (saddleCoordinates e (X t)) p < 1 by have hh := hstay t ht.1; linarith)
    have hBY := middle_unit_neighborhood_B_bounds z H hz (saddleCoordinates e (Y t))
      (lt_of_le_of_lt (hYclosed t ht) hr1)
    have hv := (saddleCoordinates_hasDerivAt e he hu X hX t ht.1 hBX).sub
      (saddleCoordinates_hasDerivAt e he hu Y hY t ht.1 hBY)
    exact perturbedSaddleQuadratic_hasDerivAt e z α (by linarith [hz.1]) v _ t hv
  have hdec : ∀ t ∈ Icc 0 τ, dq t ≤ 0 := by
    intro t ht
    have hh := hpair (saddleCoordinates e (X t)) (saddleCoordinates e (Y t))
      (show dist (saddleCoordinates e (X t)) p < δ by have hh := hstay t ht.1; linarith)
      (lt_of_le_of_lt (hYclosed t ht) hrδ)
    have hn := mul_nonneg hη.le (sq_nonneg ‖v t‖)
    change dq t ≤ -(η*‖v t‖^2) at hh
    linarith only [hh,hn]
  have hnegative := negative_through_interval (pairConeValue e z α X Y) dq τ hτ.1.le hd hdec hstart
  refine ⟨τ,hτ.1,hlevel,hbefore,hnegative,?_⟩
  intro t ht
  have hb := perturbed_negative_B_ne_zero e z α hz hα.le (v t) (hnegative t ht).2
  change (X t).B-(Y t).B ≠ 0 at hb
  exact sub_ne_zero.mp hb

theorem middle_first_exit_retains_margin (e z H : ℝ)
    (he : 0 ≤ e) (hu : e ≤ 1/50000) (hz : z ∈ Icc (19/10:ℝ) (21/10)) :
    ∃ α r : ℝ, 0 < α ∧ 0 < r ∧
      perturbedSaddleQuadratic e z α
        ![-(60/(z+2))/(z+2),1,(16+4*z)/(20001/10000),0] < 0 ∧
      ∀ X Y : ℝ → State, IsPositiveTrajectory e X → IsPositiveTrajectory e Y →
      (∀ t : ℝ, 0 ≤ t → dist (saddleCoordinates e (X t)) ![60/(z+2),z,H,0] < r/2) →
      dist (saddleCoordinates e (Y 0)) ![60/(z+2),z,H,0] < r →
      pairConeValue e z α X Y 0 < 0 →
      ∃ τ : ℝ, 0 < τ ∧ dist (saddleCoordinates e (Y τ)) ![60/(z+2),z,H,0] = r ∧
        (∀ t ∈ Ico 0 τ, dist (saddleCoordinates e (Y t)) ![60/(z+2),z,H,0] < r) ∧
        (∀ t ∈ Icc 0 τ, pairConeValue e z α X Y t ≤ pairConeValue e z α X Y 0 ∧
          pairConeValue e z α X Y t < 0) ∧
        (∀ t ∈ Icc 0 τ, (X t).B ≠ (Y t).B) := by
  obtain ⟨α,d,hα,hd,hv,hexit⟩ := middle_first_exit_at_radius e z H he hu hz
  refine ⟨α,d/2,hα,by positivity,hv,?_⟩
  exact hexit (d/2) (by positivity) (by linarith)

end CoreCouplingGlobal
