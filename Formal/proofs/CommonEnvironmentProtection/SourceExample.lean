import proofs.CommonEnvironmentProtection.SourceFamilies

namespace CommonEnvironmentProtection.SourceExample
noncomputable section
open SourceFamilies PrivateBranches CoupledPrivate

/-- Published model constants after unit conversion; maintained peroxide 0.01 uM
is a design condition. These are not a newly calibrated clinical preparation. -/
def glutathione : Glutathione where
  a := 21/100
  b := 1/25
  c := 10
  E := 50
  total := 368+2*(89/50)
  baseline := 89/50
  k := 16/5
  ha := by norm_num
  hb := by norm_num
  hc := by norm_num
  hE := by norm_num
  hk := by norm_num
  hbaseline := by norm_num
  hpool := by norm_num [gRho]

def thioredoxin : Thioredoxin where
  a := 2/5
  b := 9/12500
  c := 3/1000
  d := 15
  e := 21/10
  E := 2387/125
  total := 101/200
  baseline := 3/40
  k := 20
  ha := by norm_num
  hb := by norm_num
  hc := by norm_num
  hd := by norm_num
  he := by norm_num
  hE := by norm_num
  hk := by norm_num
  hbaseline := by norm_num
  hpool := by norm_num

theorem exact_demand_floors :
    glutathione.branch.floor 10=3294375/138400918 ∧
    thioredoxin.branch.floor 4=460180/489387 := by
  norm_num [glutathione,thioredoxin,Glutathione.branch,Thioredoxin.branch,
    Branch.floor,Branch.margin,Branch.target,gRho,tRho]

/-- Exact source-model boundary, with arbitrary positive regeneration scaling.
The minimum scale is an explicit algebraic real through the carrier square root. -/
theorem exact_joint_boundary (s : ℝ) (hs : 0<s) :
    PoolJoint glutathione thioredoxin s 375 30 (873/10) 10 4 ↔
      minimumScale glutathione.branch thioredoxin.branch 375 30 (873/10)
        (460180/489387) ≤ s := by
  have hmax : max (glutathione.branch.floor 10) (thioredoxin.branch.floor 4)=460180/489387 := by
    rw [exact_demand_floors.1,exact_demand_floors.2]
    norm_num
  rw [← hmax]
  apply pool_joint_iff_repair glutathione thioredoxin s 375 30 (873/10) 10 4 hs
  all_goals norm_num [glutathione,thioredoxin,Glutathione.branch,Thioredoxin.branch,
    Branch.floor,Branch.margin,Branch.target,gRho,tRho]

def requiredScale : ℝ := minimumScale glutathione.branch thioredoxin.branch
  375 30 (873/10) (460180/489387)

theorem certified_scale_bounds :
    (11371266:ℝ)/100000000 ≤ requiredScale ∧ requiredScale ≤ 11371268/100000000 := by
  let L : ℝ := 460180/489387
  have hglo : (3611185:ℝ)/10000 ≤ glutathione.branch.carrier L := by
    apply (QuadraticPool.polynomial_le_iff _ _ _ _ glutathione.branch.ha
      glutathione.branch.hd (by norm_num)).mp
    norm_num [L,glutathione,Glutathione.branch,gRho]
  have hghi : glutathione.branch.carrier L ≤ (3611186:ℝ)/10000 := by
    by_contra! hh
    have hp := (QuadraticPool.polynomial_le_iff _ _ _ _ glutathione.branch.ha
      glutathione.branch.hd (show (0:ℝ)≤3611186/10000 by norm_num)).mpr hh.le
    norm_num [L,glutathione,Glutathione.branch,gRho] at hp
  have ht : thioredoxin.branch.carrier L=(5000:ℝ)/23009 := by
    symm
    apply QuadraticPool.positive_root_unique _ _ _ _ thioredoxin.branch.ha
      thioredoxin.branch.hd (by norm_num)
    norm_num [L,thioredoxin,Thioredoxin.branch,tRho]
  have htflux : thioredoxin.branch.flux L=4 := by
    unfold Branch.flux
    rw [ht]
    norm_num [thioredoxin,Thioredoxin.branch,tRho,QuadraticPool.rate]
  have hflo := (QuadraticPool.rate_strictMono _ _ _ glutathione.branch.hp
    glutathione.branch.hu glutathione.branch.hv).monotoneOn
      (show (0:ℝ)≤3611185/10000 by norm_num) (glutathione.branch.carrier_pos L).le hglo
  have hfhi := (QuadraticPool.rate_strictMono _ _ _ glutathione.branch.hp
    glutathione.branch.hu glutathione.branch.hv).monotoneOn
      (glutathione.branch.carrier_pos L).le (show (0:ℝ)≤3611186/10000 by norm_num) hghi
  have hb : 0<MaintainedSource.supply 1 375 30 (873/10) L := by
    norm_num [L,MaintainedSource.supply]
  change (11371266:ℝ)/100000000 ≤ minimumScale glutathione.branch thioredoxin.branch
      375 30 (873/10) L ∧ minimumScale glutathione.branch thioredoxin.branch
      375 30 (873/10) L ≤ 11371268/100000000
  unfold minimumScale
  rw [htflux,le_div_iff₀ hb,div_le_iff₀ hb]
  constructor
  · have hc : (11371266:ℝ)/100000000*MaintainedSource.supply 1 375 30 (873/10) L ≤
        QuadraticPool.rate glutathione.branch.p glutathione.branch.u glutathione.branch.v
          (3611185/10000)+4 := by
      norm_num [L,MaintainedSource.supply,QuadraticPool.rate,glutathione,Glutathione.branch,gRho]
    change QuadraticPool.rate glutathione.branch.p glutathione.branch.u glutathione.branch.v
      (3611185/10000) ≤ glutathione.branch.flux L at hflo
    linarith
  · have hc : QuadraticPool.rate glutathione.branch.p glutathione.branch.u glutathione.branch.v
        (3611186/10000)+4 ≤ (11371268:ℝ)/100000000*MaintainedSource.supply 1 375 30 (873/10) L := by
      norm_num [L,MaintainedSource.supply,QuadraticPool.rate,glutathione,Glutathione.branch,gRho]
    change glutathione.branch.flux L ≤ QuadraticPool.rate glutathione.branch.p
      glutathione.branch.u glutathione.branch.v (3611186/10000) at hfhi
    linarith

theorem initial_joint_fails : ¬PoolJoint glutathione thioredoxin (1/10) 375 30 (873/10) 10 4 := by
  rw [exact_joint_boundary _ (by norm_num)]
  have h := certified_scale_bounds.1
  change ¬ requiredScale ≤ 1/10
  linarith

theorem certified_repair_passes :
    PoolJoint glutathione thioredoxin (11371268/100000000) 375 30 (873/10) 10 4 := by
  rw [exact_joint_boundary _ (by norm_num)]
  exact certified_scale_bounds.2

end
end CommonEnvironmentProtection.SourceExample
