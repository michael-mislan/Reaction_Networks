import proofs.CoreCouplingGlobal.FiniteFlowDifferential

namespace CoreCouplingGlobal
open Set Filter
open scoped Topology ContDiff

/-- Analytic inverse germs restrict to an actual open partial homeomorphism,
with both directions analytic and its source inside a requested neighborhood. -/
theorem analytic_inverse_germs_chart (F R : ResponseVector → ResponseVector)
    (p q : ResponseVector) (hF0 : F p=q)
    (hF : ContDiffAt ℝ ω F p) (hR : ContDiffAt ℝ ω R q)
    (hl : ∀ᶠ x in 𝓝 p, R (F x)=x) (hr : ∀ᶠ y in 𝓝 q, F (R y)=y)
    (A : Set ResponseVector) (hA : A ∈ 𝓝 p) :
    ∃ H : OpenPartialHomeomorph ResponseVector ResponseVector,
      (H : ResponseVector → ResponseVector)=F ∧
      (H.symm : ResponseVector → ResponseVector)=R ∧ p ∈ H.source ∧
      H.source ⊆ A ∧ ContDiffOn ℝ ω H H.source ∧ ContDiffOn ℝ ω H.symm H.target := by
  have hFn := hF.eventually (by simp : (ω:ℕ∞ω) ≠ ∞)
  have hRn := hR.eventually (by simp : (ω:ℕ∞ω) ≠ ∞)
  obtain ⟨S,hSsub,hS,hpS⟩ := mem_nhds_iff.1 ((hl.and hFn).and hA)
  obtain ⟨T,hTsub,hT,hqT⟩ := mem_nhds_iff.1 (hr.and hRn)
  have hFS : ContDiffOn ℝ ω F S := fun x hx => (hSsub hx).1.2.contDiffWithinAt
  have hRT : ContDiffOn ℝ ω R T := fun x hx => (hTsub hx).2.contDiffWithinAt
  let H : OpenPartialHomeomorph ResponseVector ResponseVector :=
    { toFun := F
      invFun := R
      source := S ∩ F ⁻¹' T
      target := T ∩ R ⁻¹' S
      map_source' := by
        intro x hx
        exact ⟨hx.2,show R (F x) ∈ S from by rw [(hSsub hx.1).1.1]; exact hx.1⟩
      map_target' := by
        intro y hy
        exact ⟨hy.2,show F (R y) ∈ T from by rw [(hTsub hy.1).1]; exact hy.1⟩
      left_inv' := fun x hx => (hSsub hx.1).1.1
      right_inv' := fun y hy => (hTsub hy.1).1
      open_source := hFS.continuousOn.isOpen_inter_preimage hS hT
      open_target := hRT.continuousOn.isOpen_inter_preimage hT hS
      continuousOn_toFun := hFS.continuousOn.mono inter_subset_left
      continuousOn_invFun := hRT.continuousOn.mono inter_subset_left }
  refine ⟨H,rfl,rfl,?_,?_,?_,?_⟩
  · exact ⟨hpS,show F p ∈ T from by rw [hF0]; exact hqT⟩
  · intro x hx
    exact (hSsub hx.1).2
  · exact hFS.mono inter_subset_left
  · exact hRT.mono inter_subset_left

end CoreCouplingGlobal
