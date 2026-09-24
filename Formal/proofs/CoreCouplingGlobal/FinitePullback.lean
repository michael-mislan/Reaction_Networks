import proofs.CoreCouplingGlobal.LateBasinClosure

namespace CoreCouplingGlobal
open CoreCouplingCAC Set Filter Topology

theorem response_vector_segment_unique (e T : ℝ) (hT : 0 ≤ T)
    (X Y : ℝ → ResponseVector)
    (hX : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt X (responseVectorField e (X t)) t)
    (hY : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt Y (responseVectorField e (Y t)) t)
    (h0 : X 0 = Y 0) : X T = Y T := by
  have hcX : ContinuousOn X (Icc (0:ℝ) T) := fun t ht => (hX t ht).continuousAt.continuousWithinAt
  have hcY : ContinuousOn Y (Icc (0:ℝ) T) := fun t ht => (hY t ht).continuousAt.continuousWithinAt
  have hcompact := (isCompact_Icc.image_of_continuousOn hcX).union
    (isCompact_Icc.image_of_continuousOn hcY)
  obtain ⟨R,hR⟩ := hcompact.isBounded.subset_closedBall (0 : ResponseVector)
  obtain ⟨K,hK⟩ := (responseVectorField_contDiff e).contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (convex_closedBall (0 : ResponseVector) R)
    (isCompact_closedBall (0 : ResponseVector) R)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => responseVectorField e)
    (s := fun _ => Metric.closedBall (0:ResponseVector) R) (fun _ _ => hK)
    hcX (fun t ht => (hX t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    (fun t ht => hR (Or.inl ⟨t,⟨ht.1,ht.2.le⟩,rfl⟩))
    hcY (fun t ht => (hY t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    (fun t ht => hR (Or.inr ⟨t,⟨ht.1,ht.2.le⟩,rfl⟩)) h0 ⟨hT,le_rfl⟩

/-- Every sufficiently small perturbation of a finite endpoint has a positive
preimage arbitrarily close to the reference initial state. -/
theorem positive_trajectory_finite_pullback (e : ℝ) (he : 0 ≤ e) (hu : e ≤ 1/50000)
    (X : ℝ → State) (hX : IsPositiveTrajectory e X) (T : ℝ) (hT : 0 ≤ T)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : State,
      dist (encodeState y) (encodeState (X T)) < δ →
      ∃ Y : ℝ → State, IsPositiveTrajectory e Y ∧ Y T = y ∧
        dist (encodeState (Y 0)) (encodeState (X 0)) < ε := by
  let C : Set ResponseVector := (fun t => encodeState (X t)) '' Icc (0:ℝ) T
  have hc : ContinuousOn (fun t => encodeState (X t)) (Icc (0:ℝ) T) :=
    (positive_trajectory_vector_continuous e X hX).mono (fun _ ht => ht.1)
  have hC : IsCompact C := isCompact_Icc.image_of_continuousOn hc
  have hCD : C ⊆ positiveDomain := by
    rintro x ⟨t,ht,rfl⟩
    simpa only [positiveDomain,mem_setOf_eq,decode_encodeState] using hX.positive t ht.1
  obtain ⟨a,ha,hatube⟩ := hC.exists_thickening_subset_open positiveDomain_isOpen hCD
  obtain ⟨R,hR⟩ := hC.isBounded.subset_closedBall (0 : ResponseVector)
  have hR0 : 0 ≤ R := by
    have hh := hR (show encodeState (X 0) ∈ C from ⟨0,⟨le_rfl,hT⟩,rfl⟩)
    exact (dist_nonneg : 0 ≤ dist (encodeState (X 0)) 0).trans hh
  let b : ContDiffBump (0 : ResponseVector) := ⟨R+1,2*(R+1),by linarith,by linarith⟩
  let f : ResponseVector → ResponseVector := fun x => b x • responseVectorField e x
  have hfcompact : HasCompactSupport f := b.hasCompactSupport.smul_right
  have hfdiff : ContDiff ℝ 1 f := b.contDiff.smul (responseVectorField_contDiff e)
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hfcompact hfdiff (by norm_num)
  obtain ⟨L,hL⟩ := hfcompact.exists_bound_of_continuous hfdiff.continuous
  have hfagree : ∀ x, ‖x‖ ≤ R+1 → f x = responseVectorField e x := by
    intro x hx
    have hb : b x = 1 := b.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hx)
    simp only [f,hb,one_smul]
  have hXnorm : ∀ t ∈ Icc (0:ℝ) T, ‖encodeState (X t)‖ ≤ R := by
    intro t ht
    simpa only [Metric.mem_closedBall,dist_zero_right] using hR ⟨t,ht,rfl⟩
  let q := min ε (min a 1)
  have hq : 0 < q := lt_min hε (lt_min ha (by norm_num))
  let δ := q/Real.exp (K*T)
  have hδ : 0 < δ := div_pos hq (Real.exp_pos _)
  refine ⟨δ,hδ,?_⟩
  intro y hy
  have hnegK : LipschitzWith K (fun x => -f x) := hK.neg
  obtain ⟨U,hU0,hUd⟩ := bounded_lipschitz_global_solution (fun x => -f x) K
    ⟨max L 0,le_max_right _ _⟩ hnegK
    (fun x => by simpa only [norm_neg] using (hL x).trans (le_max_left L 0)) (encodeState y)
  let V : ℝ → ResponseVector := fun t => encodeState (X (T-t))
  have hVd : ∀ t ∈ Icc (0:ℝ) T, HasDerivAt V (-f (V t)) t := by
    intro t ht
    have hts : T-t ∈ Icc (0:ℝ) T := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have hsub : HasDerivAt (fun s : ℝ => T-s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub T
    have hh := (positive_trajectory_vector_derivative e X hX (T-t) hts.1).scomp t hsub
    have hn := hXnorm (T-t) hts
    rw [hfagree _ (by dsimp [V]; linarith)]
    simpa only [V,Function.comp_def,neg_one_smul] using hh
  have hbound : ∀ t ∈ Icc (0:ℝ) T, dist (U t) (V t) < q := by
    intro t ht
    have hb := dist_le_of_trajectories_ODE (v := fun _ x => -f x) (fun _ => hnegK)
      (fun s _ => (hUd s).continuousAt.continuousWithinAt)
      (fun s _ => (hUd s).hasDerivWithinAt)
      (fun s hs => (hVd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hVd s ⟨hs.1,hs.2.le⟩).hasDerivWithinAt)
      (le_refl (dist (U 0) (V 0))) t ht
    have hinit : dist (U 0) (V 0) < δ := by simpa only [hU0,V,sub_zero] using hy
    have hexp : Real.exp (K*t) ≤ Real.exp (K*T) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 K.coe_nonneg)
    have hscale := mul_le_mul_of_nonneg_left hexp (dist_nonneg : 0 ≤ dist (U 0) (V 0))
    have hsmall := (lt_div_iff₀ (Real.exp_pos (K*T))).1 hinit
    simp only [sub_zero] at hb
    exact hb.trans_lt (hscale.trans_lt hsmall)
  have hUpos : ∀ t ∈ Icc (0:ℝ) T, (decodeState (U t)).Positive := by
    intro t ht
    apply hatube
    apply Metric.mem_thickening_iff.2
    refine ⟨V t,⟨T-t,⟨by linarith [ht.2],by linarith [ht.1]⟩,rfl⟩,?_⟩
    exact (hbound t ht).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hUnorm : ∀ t ∈ Icc (0:ℝ) T, ‖U t‖ ≤ R+1 := by
    intro t ht
    have hnear : dist (U t) (V t) < 1 :=
      (hbound t ht).trans_le ((min_le_right _ _).trans (min_le_right _ _))
    have hn : ‖V t‖ ≤ R := hXnorm (T-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have hh := dist_triangle (U t) (V t) 0
    simp only [dist_zero_right] at hh
    linarith
  obtain ⟨Y,hY0,hY⟩ := positive_global_solution e he hu (decodeState (U T)) (hUpos T ⟨hT,le_rfl⟩)
  have hreverse : ∀ t ∈ Icc (0:ℝ) T,
      HasDerivAt (fun s => U (T-s)) (responseVectorField e (U (T-t))) t := by
    intro t ht
    have hts : T-t ∈ Icc (0:ℝ) T := ⟨by linarith [ht.2],by linarith [ht.1]⟩
    have hsub : HasDerivAt (fun s : ℝ => T-s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub T
    have hh := (hUd (T-t)).scomp t hsub
    simpa only [Function.comp_def,neg_one_smul,neg_neg,hfagree _ (hUnorm (T-t) hts)] using hh
  have hend := response_vector_segment_unique e T hT (fun t => encodeState (Y t)) (fun t => U (T-t))
    (fun t ht => positive_trajectory_vector_derivative e Y hY t ht.1) hreverse
    (by simp only [hY0,encode_decodeState,sub_zero])
  have hYe : Y T = y := by
    have hh := congrArg decodeState hend
    simpa only [decode_encodeState,sub_self,hU0] using hh
  refine ⟨Y,hY,hYe,?_⟩
  have hh := (hbound T ⟨hT,le_rfl⟩).trans_le (min_le_left ε (min a 1))
  simpa only [hY0,encode_decodeState,V,sub_self] using hh

end CoreCouplingGlobal
