import proofs.CommonEnvironmentProtection.Main

namespace CommonEnvironmentProtection.Postproof
noncomputable section
open CoupledPrivate SourceFamilies SourceExample LiteralSteady

theorem boundary_flux (B : Branch) (q : ℝ) (hq : 0<q)
    (hcap : 0<B.p-q*B.v) (hm : 0<B.margin q) : B.flux (B.floor q)=q := by
  have hy := B.target_pos q hq hcap
  have hx := B.floor_pos q hq hcap hm
  have he : B.carrier (B.floor q)=B.target q := by
    symm
    apply QuadraticPool.positive_root_unique _ _ _ _ B.ha B.hd hy
    dsimp [Branch.floor,Branch.margin]
    field_simp [ne_of_gt B.hc,ne_of_gt hy]
    ring
  unfold Branch.flux
  rw [he]
  dsimp [QuadraticPool.rate,Branch.target]
  field_simp [ne_of_gt B.hp,ne_of_gt B.hu]
  ring

theorem isolated_at_floor (B : Branch) (s V N D L : ℝ)
    (hs : 0<s) (hV : 0<V) (hND : N<D) (hL : 0<L) (hLN : L<N) :
    (∃! x, x ∈ Set.Icc L N ∧ MaintainedSource.supply s V N D x-B.flux x=0) ↔
      B.flux L/MaintainedSource.supply 1 V N D L ≤ s := by
  have hc : ContinuousOn (fun x => MaintainedSource.supply s V N D x-B.flux x) (Set.Icc L N) := by
    have h := MaintainedSource.drift_continuous s V N D 0 0 L N hND le_rfl
    change ContinuousOn (fun x => MaintainedSource.supply s V N D x-0*x-0) (Set.Icc L N) at h
    simp only [zero_mul,sub_zero] at h
    exact h.sub (B.flux_continuous L N hL)
  have ha : StrictAntiOn (fun x => MaintainedSource.supply s V N D x-B.flux x) (Set.Icc L N) := by
    intro x hx y hy hxy
    have h := MaintainedSource.drift_strictAnti s V N D 0 0 hs hV hND (le_refl 0) hx.2 hy.2 hxy
    simp only [MaintainedSource.drift,zero_mul,sub_zero] at h
    have hf := B.flux_strictMono (hL.trans_le hx.1) (hL.trans_le hy.1) hxy
    linarith
  rw [safe_equilibrium_iff _ _ _ hLN.le hc ha]
  have hn : MaintainedSource.supply s V N D N-B.flux N≤0 := by
    have h := B.flux_pos N
    simp [MaintainedSource.supply]; linarith
  rw [and_iff_left hn]
  have hb : 0<MaintainedSource.supply 1 V N D L := by
    unfold MaintainedSource.supply
    exact div_pos (mul_pos (mul_pos (by norm_num) hV) (sub_pos.mpr hLN)) (by linarith)
  rw [div_le_iff₀ hb]
  have he : MaintainedSource.supply s V N D L=s*MaintainedSource.supply 1 V N D L := by
    unfold MaintainedSource.supply; ring
  rw [he]
  constructor <;> intro h <;> linarith

theorem isolated_successes :
    (∃ x g, 0<x ∧ x≤30 ∧ GState.Steady g glutathione x ∧
      MaintainedSource.supply (1/10) 375 30 (873/10) x=g.j ∧ 10≤g.j) ∧
    (∃ x t, 0<x ∧ x≤30 ∧ TState.Steady t thioredoxin x ∧
      MaintainedSource.supply (1/10) 375 30 (873/10) x=t.j ∧ 4≤t.j) := by
  have hG : glutathione.branch.flux (glutathione.branch.floor 10)=10 := by
    apply boundary_flux
    all_goals norm_num [glutathione,Glutathione.branch,Branch.margin,Branch.target,PrivateBranches.gRho]
  have hT : thioredoxin.branch.flux (thioredoxin.branch.floor 4)=4 := by
    apply boundary_flux
    all_goals norm_num [thioredoxin,Thioredoxin.branch,Branch.margin,Branch.target,PrivateBranches.tRho]
  have exG := (isolated_at_floor glutathione.branch (1/10) 375 30 (873/10)
    (glutathione.branch.floor 10) (by norm_num) (by norm_num) (by norm_num)
    (by rw [exact_demand_floors.1]; norm_num) (by rw [exact_demand_floors.1]; norm_num)).mpr
    (show glutathione.branch.flux (glutathione.branch.floor 10)/MaintainedSource.supply 1 375 30 (873/10) (glutathione.branch.floor 10)≤1/10 by
      rw [hG,exact_demand_floors.1]; norm_num [MaintainedSource.supply])
  have exT := (isolated_at_floor thioredoxin.branch (1/10) 375 30 (873/10)
    (thioredoxin.branch.floor 4) (by norm_num) (by norm_num) (by norm_num)
    (by rw [exact_demand_floors.2]; norm_num) (by rw [exact_demand_floors.2]; norm_num)).mpr
    (show thioredoxin.branch.flux (thioredoxin.branch.floor 4)/MaintainedSource.supply 1 375 30 (873/10) (thioredoxin.branch.floor 4)≤1/10 by
      rw [hT,exact_demand_floors.2]; norm_num [MaintainedSource.supply])
  constructor
  · obtain ⟨x,⟨hx,hbal⟩,_⟩ := exG
    have hxp : 0<x := lt_of_lt_of_le (by rw [exact_demand_floors.1]; norm_num) hx.1
    have hp := (glutathione.pool_iff x _ hxp (glutathione.branch.carrier_pos x)).mpr
      (QuadraticPool.root_balance _ _ _ glutathione.branch.ha glutathione.branch.hd)
    refine ⟨x,reconstructG glutathione x (glutathione.branch.carrier x),hxp,hx.2,
      reconstructG_steady _ _ _ hxp (glutathione.branch.carrier_pos x) hp,?_,?_⟩
    · change _=PrivateBranches.gFlux _ _ _ _ _
      rw [← glutathione.rate_eq]
      change _=glutathione.branch.flux x
      linarith
    · change 10≤PrivateBranches.gFlux _ _ _ _ _
      rw [← glutathione.rate_eq]
      change 10≤glutathione.branch.flux x
      rw [← hG]
      exact glutathione.branch.flux_strictMono.monotoneOn
        (by rw [exact_demand_floors.1]; norm_num) hxp hx.1
  · obtain ⟨x,⟨hx,hbal⟩,_⟩ := exT
    have hxp : 0<x := lt_of_lt_of_le (by rw [exact_demand_floors.2]; norm_num) hx.1
    have hp := (thioredoxin.pool_iff x _ hxp (thioredoxin.branch.carrier_pos x)).mpr
      (QuadraticPool.root_balance _ _ _ thioredoxin.branch.ha thioredoxin.branch.hd)
    refine ⟨x,reconstructT thioredoxin x (thioredoxin.branch.carrier x),hxp,hx.2,
      reconstructT_steady _ _ _ hxp (thioredoxin.branch.carrier_pos x) hp,?_,?_⟩
    · change _=PrivateBranches.tFlux _ _ _ _ _ _ _
      rw [← thioredoxin.rate_eq]
      change _=thioredoxin.branch.flux x
      linarith
    · change 4≤PrivateBranches.tFlux _ _ _ _ _ _ _
      rw [← thioredoxin.rate_eq]
      change 4≤thioredoxin.branch.flux x
      rw [← hT]
      exact thioredoxin.branch.flux_strictMono.monotoneOn
        (by rw [exact_demand_floors.2]; norm_num) hxp hx.1

theorem overdelivery_identity (jG jT qG qT R : ℝ) :
    (jG+jT)/R-(qG+qT)/R=((jG-qG)+(jT-qT))/R := by ring

theorem overdelivery_nonnegative (jG jT qG qT R : ℝ)
    (hG : qG≤jG) (hT : qT≤jT) (hR : 0<R) :
    0≤((jG-qG)+(jT-qT))/R ∧
    (((jG-qG)+(jT-qT))/R=0 ↔ jG=qG ∧ jT=qT) := by
  constructor
  · exact div_nonneg (by linarith) hR.le
  · rw [div_eq_zero_iff]
    constructor
    · intro h
      have hh := h.resolve_right (ne_of_gt hR)
      constructor <;> linarith
    · rintro ⟨rfl,rfl⟩; simp

theorem robust_command (m command eps : ℝ) (hc : 0≤command) (he : 0≤eps) (he1 : eps<1) :
    (∀ eta ∈ Set.Icc (1-eps) (1+eps), m≤eta*command) ↔ m/(1-eps)≤command := by
  rw [div_le_iff₀ (sub_pos.mpr he1)]
  constructor
  · intro h
    have hh := h (1-eps) ⟨le_rfl,by linarith⟩
    nlinarith
  · intro h eta heta
    nlinarith [mul_nonneg hc (sub_nonneg.mpr heta.1)]

theorem binding_floor (xG xG' xT : ℝ) (hG : xG≤xT) (hG' : xG'≤xT) :
    max xG xT=max xG' xT := by rw [max_eq_right hG,max_eq_right hG']

theorem ceiling_obstruction (B : Branch) (q x N : ℝ) (hx : 0<x) (hxN : x<N)
    (hq : B.flux N≤q) : ¬q≤B.flux x := by
  have h := B.flux_strictMono hx (hx.trans hxN) hxN
  linarith

end
end CommonEnvironmentProtection.Postproof
