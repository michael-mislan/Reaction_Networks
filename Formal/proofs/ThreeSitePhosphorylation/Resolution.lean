import proofs.ThreeSitePhosphorylation.SourceOrbits

/-! Source-level Hopf capacity of the literal sequential distributive three-site
cycle: a transverse imaginary pair and arbitrarily small positive nonconstant
periodic solutions on one fixed compatibility class. -/
namespace ThreeSitePhosphorylation
noncomputable section
open scoped Topology

theorem three_site_hopf_capacity : ∃ r₀ w : ℝ, ∃ g : ℝ → ℂ,
    0<r₀ ∧ 0<w ∧ ContDiffAt ℝ ⊤ g r₀ ∧ g r₀=Complex.I*(w:ℂ) ∧
    HasDerivAt (fun s => (g s).re) (deriv g r₀).re r₀ ∧ (deriv g r₀).re<0 ∧
    (∀ᶠ s in 𝓝 r₀, ∃ v : Fin 9 → ℂ, v ≠ 0 ∧ (complexSource s).mulVec v=g s • v) ∧
    ∀ ε : ℝ, 0<ε → ∃ (r T : ℝ) (φ : ℝ → State),
      0<r ∧ 0<T ∧ (∀ i, 0<witnessRates r i) ∧
      |r-r₀|<ε ∧ |T-2*Real.pi/w|<ε ∧ Function.Periodic φ T ∧
      (∀ s, HasDerivAt φ (field (witnessRates r) (φ s)) s) ∧
      (∀ s i, 0<φ s i) ∧ (∀ s, ‖φ s-witnessState‖<ε) ∧
      (∀ s, totalE (φ s)=totalE witnessState ∧ totalF (φ s)=totalF witnessState ∧
        totalS (φ s)=totalS witnessState) ∧ ∃ s, φ s ≠ φ 0 := by
  obtain ⟨r₀,w,g,hr,hw,hg,hgr,hd,hcross,hspec⟩ := source_transverse_eigenvalue_branch
  obtain ⟨v,hv,he⟩ := hspec.self_of_nhds
  rw [hgr] at he
  have hp := source_eigenvalue_root r₀ (Complex.I*(w:ℂ)) v hv he
  obtain ⟨C⟩ := closed_path_family_exists r₀ w hw hp
  refine ⟨r₀,w,g,hr,hw,hg,hgr,hd,hcross,hspec,?_⟩
  intro ε hε
  have hevent := (family_small_source_orbits C hr hw hp ε hε).and
    (family_parameters_near C hr hw ε hε)
  obtain ⟨δ,hδ,hball⟩ := Metric.eventually_nhds_iff.mp hevent
  have ha : (δ/2:ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hin : dist (δ/2) (0:ℝ)<δ := by
    rw [Real.dist_eq,sub_zero,abs_of_pos (by linarith)]
    linarith
  obtain ⟨horbit,hr',hT,hrnear,hTnear⟩ := hball hin
  obtain ⟨φ,hper,hode,hprop,hnon⟩ := horbit ha
  refine ⟨(C.parameters (δ/2)).2.re,(C.parameters (δ/2)).2.im,φ,
    hr',hT,witness_rates_positive _ hr',hrnear,hTnear,hper,hode,?_,?_,?_,hnon⟩
  · exact fun s => (hprop s).1
  · exact fun s => (hprop s).2.1
  · exact fun s => (hprop s).2.2

end
end ThreeSitePhosphorylation
