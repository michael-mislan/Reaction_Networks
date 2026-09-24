import proofs.CommonEnvironmentProtection.Postproof

namespace CommonEnvironmentProtection.Allocation
noncomputable section
open CoupledPrivate SourceFamilies SourceExample LiteralSteady PrivateBranches

def L : ℝ := 460180/489387
def A : ℝ := 368-20/((16/5)*L)
def gStar : ℝ := 361+QuadraticPool.root 1 (722-A) (361*A-361^2-1)

theorem gStar_properties : 361<gStar ∧ gStar<362 ∧ gStar^2-A*gStar+1=0 := by
  have hd : 0<361*A-361^2-1 := by norm_num [A,L]
  have hp := QuadraticPool.root_pos 1 (722-A) _ (by norm_num) hd
  have hb := QuadraticPool.root_balance 1 (722-A) _ (by norm_num) hd
  have hu : QuadraticPool.root 1 (722-A) (361*A-361^2-1)<1 := by
    by_contra! h
    have hh := (QuadraticPool.polynomial_le_iff 1 (722-A) _ 1 (by norm_num) hd (by norm_num)).mpr h
    norm_num [A,L] at hh
  dsimp [gStar]
  constructor
  · linarith
  constructor
  · linarith
  · nlinarith

def eStar : ℝ := 10*(gStar+gRho (21/100) (1/25) 10)/((21/100)*gStar)

theorem eStar_bounds : 0<eStar ∧ eStar<50 := by
  have hg := gStar_properties.1
  have hd : 0<(21:ℝ)/100*gStar := by positivity
  constructor
  · apply div_pos _ hd
    norm_num [gRho]
    positivity
  · rw [eStar,div_lt_iff₀ hd]
    norm_num [gRho]
    linarith

def redesigned : Glutathione := { glutathione with
  E := eStar
  hE := eStar_bounds.1
  hpool := by
    have h := eStar_bounds.2
    change 0<(glutathione.total-2*glutathione.baseline)*gRho glutathione.a glutathione.b glutathione.c-eStar*glutathione.a/glutathione.c
    norm_num [glutathione,gRho]
    linarith }

theorem redesigned_flux : gFlux redesigned.a redesigned.b redesigned.c redesigned.E gStar=10 := by
  have hg : gStar≠0 := ne_of_gt (lt_trans (by norm_num) gStar_properties.1)
  have hr : gStar+gRho (21/100) (1/25) 10≠0 := by
    have h := gStar_properties.1
    norm_num [gRho]
    linarith
  dsimp [redesigned,glutathione,eStar,gFlux]
  field_simp [hg,hr]

theorem redesigned_pool :
    gStar+2*(redesigned.baseline+gFlux redesigned.a redesigned.b redesigned.c redesigned.E gStar/(redesigned.k*L))+
      gFlux redesigned.a redesigned.b redesigned.c redesigned.E gStar/(redesigned.c*gStar)=redesigned.total := by
  rw [redesigned_flux]
  have hg : gStar≠0 := ne_of_gt (lt_trans (by norm_num) gStar_properties.1)
  have hb := gStar_properties.2.2
  norm_num [A,L] at hb
  dsimp [redesigned,glutathione,L]
  field_simp [hg]
  nlinarith

def quotaScale : ℝ := 14/MaintainedSource.supply 1 375 30 (873/10) L

theorem allocation_attained : FullJoint redesigned thioredoxin quotaScale 375 30 (873/10) 10 4 := by
  let y : ℝ := 5000/23009
  have ht : tFlux thioredoxin.a thioredoxin.b thioredoxin.c thioredoxin.d thioredoxin.e thioredoxin.E y=4 := by
    norm_num [thioredoxin,tFlux,tRho,y]
  have hp : y+thioredoxin.baseline+tFlux thioredoxin.a thioredoxin.b thioredoxin.c thioredoxin.d thioredoxin.e thioredoxin.E y/(thioredoxin.k*L)=thioredoxin.total := by
    rw [ht]; norm_num [y,thioredoxin,L]
  refine ⟨L,reconstructG redesigned L gStar,reconstructT thioredoxin L y,
    by norm_num [L],by norm_num [L],
    reconstructG_steady _ _ _ (by norm_num [L]) (lt_trans (by norm_num) gStar_properties.1) redesigned_pool,
    reconstructT_steady _ _ _ (by norm_num [L]) (by norm_num [y]) hp,?_,?_,?_⟩
  · change _=gFlux _ _ _ _ _+tFlux _ _ _ _ _ _ _
    rw [redesigned_flux,ht]
    norm_num [quotaScale,MaintainedSource.supply,L]
  · change 10≤gFlux _ _ _ _ _
    rw [redesigned_flux]
  · change 4≤tFlux _ _ _ _ _ _ _
    rw [ht]

/-- Lower bound holds for every admitted glutathione redesign, and hence in
particular for enzyme-only redesigns with all carrier totals fixed. -/
theorem allocation_lower_bound (G : Glutathione) (s : ℝ) (hs : 0<s)
    (h : FullJoint G thioredoxin s 375 30 (873/10) 10 4) : quotaScale≤s := by
  obtain ⟨x,g,t,hx,hN,hg,ht,hbal,hqg,hqt⟩ := h
  obtain ⟨ej,ep⟩ := t.eliminate thioredoxin x hx ht
  have er : t.y=thioredoxin.branch.carrier x :=
    QuadraticPool.positive_root_unique _ _ _ _ thioredoxin.branch.ha thioredoxin.branch.hd ht.1
      ((thioredoxin.pool_iff x t.y hx ht.1).mp ep)
  have ef : t.j=thioredoxin.branch.flux x := by
    rw [ej,er,← thioredoxin.rate_eq]
    rfl
  have hf : L≤x := by
    rw [ef] at hqt
    have h := (thioredoxin.branch.service_iff 4 x (by norm_num) hx
      (by norm_num [thioredoxin,Thioredoxin.branch,tRho])
      (by norm_num [thioredoxin,Thioredoxin.branch,Branch.margin,Branch.target,tRho])).mp hqt
    simpa only [exact_demand_floors.2,L] using h
  have hsup := (MaintainedSource.drift_strictAnti s 375 30 (873/10) 0 0 hs
    (by norm_num) (by norm_num) (le_refl 0)).antitoneOn (show L≤30 by norm_num [L]) hN hf
  simp only [MaintainedSource.drift,zero_mul,sub_zero] at hsup
  have hb : 0<MaintainedSource.supply 1 375 30 (873/10) L := by norm_num [MaintainedSource.supply,L]
  rw [quotaScale,div_le_iff₀ hb]
  have he : MaintainedSource.supply s 375 30 (873/10) L=s*MaintainedSource.supply 1 375 30 (873/10) L := by
    unfold MaintainedSource.supply; ring
  rw [he] at hsup
  linarith

theorem original_source_insufficient_for_redesign (G : Glutathione) :
    ¬FullJoint G thioredoxin (1/10) 375 30 (873/10) 10 4 := by
  intro h
  have hh := allocation_lower_bound G (1/10) (by norm_num) h
  norm_num [quotaScale,MaintainedSource.supply,L] at hh

end
end CommonEnvironmentProtection.Allocation
