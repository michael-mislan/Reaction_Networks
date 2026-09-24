import proofs.CoreCouplingGlobal.FinitePhysicalFlow

namespace CoreCouplingGlobal
open Set Filter
open scoped Topology ContDiff

theorem scaled_physical_segment_unique (e σ T : ℝ) (hT : 0 ≤ T)
    (X Y : ℝ → ResponseVector)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (σ • responseVectorField e (X t)) t)
    (hY : ∀ t ∈ Icc 0 T, HasDerivAt Y (σ • responseVectorField e (Y t)) t)
    (h0 : X 0=Y 0) : X T=Y T := by
  have hcX : ContinuousOn X (Icc 0 T) := fun t ht => (hX t ht).continuousAt.continuousWithinAt
  have hcY : ContinuousOn Y (Icc 0 T) := fun t ht => (hY t ht).continuousAt.continuousWithinAt
  have hc := (isCompact_Icc.image_of_continuousOn hcX).union
    (isCompact_Icc.image_of_continuousOn hcY)
  obtain ⟨R,hR⟩ := hc.isBounded.subset_closedBall (0:ResponseVector)
  have hf : ContDiff ℝ 1 (fun x => σ • responseVectorField e x) :=
    ContDiff.const_smul σ (responseVectorField_contDiff e)
  obtain ⟨K,hK⟩ := hf.contDiffOn.exists_lipschitzOnWith
    (by norm_num : (1:WithTop ℕ∞) ≠ 0) (convex_closedBall (0:ResponseVector) R)
    (isCompact_closedBall (0:ResponseVector) R)
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ x => σ • responseVectorField e x)
    (s := fun _ => Metric.closedBall (0:ResponseVector) R) (fun _ _ => hK)
    hcX (fun t ht => (hX t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    (fun t ht => hR (Or.inl ⟨t,⟨ht.1,ht.2.le⟩,rfl⟩))
    hcY (fun t ht => (hY t ⟨ht.1,ht.2.le⟩).hasDerivWithinAt)
    (fun t ht => hR (Or.inr ⟨t,⟨ht.1,ht.2.le⟩,rfl⟩)) h0 ⟨hT,le_rfl⟩

theorem physical_segment_reverse (e σ T : ℝ) (X : ℝ → ResponseVector)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (σ • responseVectorField e (X t)) t) :
    ∀ t ∈ Icc 0 T, HasDerivAt (fun u => X (T-u))
      ((-σ) • responseVectorField e (X (T-t))) t := by
  intro t ht
  have hsub : HasDerivAt (fun u : ℝ => T-u) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub T
  have hh := (hX (T-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩).scomp t hsub
  simpa only [Function.comp_def,neg_one_smul,neg_smul,one_smul] using hh

/-- Finite-time endpoint map in absolute initial coordinates, retaining actual
trajectories and arbitrary finite-segment proximity. -/
theorem physical_finite_endpoint (e σ T : ℝ) (hT : 0 ≤ T)
    (X : ℝ → ResponseVector)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (σ • responseVectorField e (X t)) t) :
    ∃ F : ResponseVector → ResponseVector,
      F (X 0)=X T ∧ ContDiffAt ℝ ω F (X 0) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ x in 𝓝 (X 0), ∃ Y : ℝ → ResponseVector,
        Y 0=x ∧ Y T=F x ∧
        (∀ t ∈ Icc 0 T, HasDerivAt Y (σ • responseVectorField e (Y t)) t) ∧
        ∀ t ∈ Icc 0 T, dist (Y t) (X t) < ε := by
  obtain ⟨Φ,h0,hcd,hfam⟩ := physical_finite_analytic_family e σ T hT X hX
  let F := fun x => Φ (x-X 0)
  have hd : ContDiffAt ℝ ω (fun x : ResponseVector => x-X 0) (X 0) :=
    contDiffAt_id.sub contDiffAt_const
  have hreg : ContDiffAt ℝ ω F (X 0) := by
    have hc : ContDiffAt ℝ ω Φ (X 0-X 0) := by simpa only [sub_self] using hcd
    exact hc.comp (f := fun x : ResponseVector => x-X 0) (X 0) hd
  refine ⟨F,by simpa only [F,sub_self] using h0,hreg,?_⟩
  intro ε hε
  have hlim : Tendsto (fun x : ResponseVector => x-X 0) (𝓝 (X 0)) (𝓝 0) := by
    simpa only [sub_self] using hd.continuousAt.tendsto
  filter_upwards [hlim.eventually (hfam ε hε)] with x hx
  obtain ⟨Y,hY0,hYT,hYd,hclose⟩ := hx
  exact ⟨Y,by simpa only [add_sub_cancel] using hY0,hYT,hYd,hclose⟩

/-- Forward and reversed actual endpoint families are inverse as germs. This
asserts no global backward completeness of the physical system. -/
theorem physical_finite_inverse_germs (e σ T : ℝ) (hT : 0 ≤ T)
    (X : ℝ → ResponseVector)
    (hX : ∀ t ∈ Icc 0 T, HasDerivAt X (σ • responseVectorField e (X t)) t) :
    ∃ F R : ResponseVector → ResponseVector,
      F (X 0)=X T ∧ R (X T)=X 0 ∧
      ContDiffAt ℝ ω F (X 0) ∧ ContDiffAt ℝ ω R (X T) ∧
      (∀ᶠ x in 𝓝 (X 0), R (F x)=x) ∧
      (∀ᶠ y in 𝓝 (X T), F (R y)=y) ∧
      (∀ᶠ x in 𝓝 (X 0), ∃ Y : ℝ → ResponseVector, Y 0=x ∧ Y T=F x ∧
        ∀ t ∈ Icc 0 T, HasDerivAt Y (σ • responseVectorField e (Y t)) t) := by
  let Z := fun t => X (T-t)
  have hZ := physical_segment_reverse e σ T X hX
  obtain ⟨F,hF0,hFcd,hFfam⟩ := physical_finite_endpoint e σ T hT X hX
  obtain ⟨R,hR0,hRcd,hRfam⟩ := physical_finite_endpoint e (-σ) T hT Z hZ
  have hZ0 : Z 0=X T := by simp [Z]
  have hZT : Z T=X 0 := by simp [Z]
  rw [hZ0,hZT] at hR0
  rw [hZ0] at hRcd hRfam
  have hF := hFfam 1 (by norm_num)
  have hR := hRfam 1 (by norm_num)
  have hFlim : Tendsto F (𝓝 (X 0)) (𝓝 (X T)) := by
    simpa only [hF0] using hFcd.continuousAt.tendsto
  have hRlim : Tendsto R (𝓝 (X T)) (𝓝 (X 0)) := by
    simpa only [hR0] using hRcd.continuousAt.tendsto
  refine ⟨F,R,hF0,hR0,hFcd,hRcd,?_,?_,?_⟩
  · filter_upwards [hF,hFlim.eventually hR] with x hx hfx
    obtain ⟨Y,hY0,hYT,hYd,_hclose⟩ := hx
    obtain ⟨W,hW0,hWT,hWd,_hcloseW⟩ := hfx
    have heq := scaled_physical_segment_unique e (-σ) T hT
      (fun t => Y (T-t)) W (physical_segment_reverse e σ T Y hYd) hWd (by
        simpa only [sub_zero,hYT] using hW0.symm)
    simpa only [sub_self,hY0,hWT] using heq.symm
  · filter_upwards [hR,hRlim.eventually hF] with y hy hry
    obtain ⟨W,hW0,hWT,hWd,_hclose⟩ := hy
    obtain ⟨Y,hY0,hYT,hYd,_hcloseY⟩ := hry
    have hrev : ∀ t ∈ Icc 0 T, HasDerivAt (fun u => W (T-u))
        (σ • responseVectorField e (W (T-t))) t := by
      simpa only [neg_neg] using physical_segment_reverse e (-σ) T W hWd
    have heq := scaled_physical_segment_unique e σ T hT
      (fun t => W (T-t)) Y hrev hYd (by
        simpa only [sub_zero,hWT] using hY0.symm)
    simpa only [sub_self,hW0,hYT] using heq.symm
  · filter_upwards [hF] with x hx
    obtain ⟨Y,h0,hT,hY,_hclose⟩ := hx
    exact ⟨Y,h0,hT,hY⟩

end CoreCouplingGlobal
