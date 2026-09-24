import proofs.CommonEnvironmentProtection.PrivateBranches
import proofs.CommonEnvironmentProtection.CoupledPrivate

namespace CommonEnvironmentProtection.SourceFamilies
noncomputable section
open PrivateBranches QuadraticPool CoupledPrivate

structure Glutathione where
  a : ℝ
  b : ℝ
  c : ℝ
  E : ℝ
  total : ℝ
  baseline : ℝ
  k : ℝ
  ha : 0 < a
  hb : 0 < b
  hc : 0 < c
  hE : 0 < E
  hk : 0 < k
  hbaseline : 0 ≤ baseline
  hpool : 0 < (total-2*baseline)*gRho a b c-E*a/c

def Glutathione.branch (S : Glutathione) : Branch where
  a := 1
  b := gRho S.a S.b S.c-(S.total-2*S.baseline)
  c := 2*S.E*S.a/S.k
  d := (S.total-2*S.baseline)*gRho S.a S.b S.c-S.E*S.a/S.c
  p := S.E*S.a
  u := gRho S.a S.b S.c
  v := 1
  ha := by norm_num
  hc := div_pos (mul_pos (mul_pos (by norm_num) S.hE) S.ha) S.hk
  hd := S.hpool
  hp := mul_pos S.hE S.ha
  hu := g_rho_pos _ _ _ S.ha S.hb S.hc
  hv := by norm_num

structure Thioredoxin where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  e : ℝ
  E : ℝ
  total : ℝ
  baseline : ℝ
  k : ℝ
  ha : 0 < a
  hb : 0 ≤ b
  hc : 0 < c
  hd : 0 < d
  he : 0 < e
  hE : 0 < E
  hk : 0 < k
  hbaseline : 0 ≤ baseline
  hpool : 0 < total-baseline

theorem Thioredoxin.rho_pos (S : Thioredoxin) : 0 < tRho S.a S.b S.c S.d := by
  unfold tRho
  exact add_pos_of_pos_of_nonneg (add_pos (one_div_pos.mpr S.ha) (one_div_pos.mpr S.hd))
    (div_nonneg S.hb (mul_pos S.hc S.hd).le)

def Thioredoxin.branch (S : Thioredoxin) : Branch where
  a := tRho S.a S.b S.c S.d*S.e
  b := 1-(S.total-S.baseline)*tRho S.a S.b S.c S.d*S.e
  c := S.E*S.e/S.k
  d := S.total-S.baseline
  p := S.E*S.e
  u := 1
  v := tRho S.a S.b S.c S.d*S.e
  ha := mul_pos S.rho_pos S.he
  hc := div_pos (mul_pos S.hE S.he) S.hk
  hd := S.hpool
  hp := mul_pos S.hE S.he
  hu := by norm_num
  hv := (mul_pos S.rho_pos S.he).le

theorem Glutathione.rate_eq (S : Glutathione) (g : ℝ) :
    rate S.branch.p S.branch.u S.branch.v g = gFlux S.a S.b S.c S.E g := by
  simp [branch,rate,gFlux,add_comm]

theorem Thioredoxin.rate_eq (S : Thioredoxin) (y : ℝ) :
    rate S.branch.p S.branch.u S.branch.v y = tFlux S.a S.b S.c S.d S.e S.E y := by
  dsimp [branch,rate,tFlux]
  congr 1
  ring

theorem Glutathione.pool_iff (S : Glutathione) (x g : ℝ) (hx : 0 < x) (hg : 0 < g) :
    g+2*(S.baseline+gFlux S.a S.b S.c S.E g/(S.k*x))+
      gFlux S.a S.b S.c S.E g/(S.c*g)=S.total ↔
    S.branch.a*g^2+(S.branch.b+S.branch.c/x)*g-S.branch.d=0 := by
  have hden : g+gRho S.a S.b S.c ≠ 0 :=
    ne_of_gt (add_pos hg (g_rho_pos _ _ _ S.ha S.hb S.hc))
  have hres := g_pool_residual S.a S.b S.c S.E S.total S.baseline S.k x g
    (ne_of_gt S.hc) (ne_of_gt S.hk) (ne_of_gt hx) (ne_of_gt hg) hden
  simp only [branch,one_mul]
  change _ ↔ gPoly S.a S.b S.c S.E S.total S.baseline S.k x g=0
  constructor
  · intro hp
    have hz : gPoly S.a S.b S.c S.E S.total S.baseline S.k x g/
        (g+gRho S.a S.b S.c)=0 := by linarith
    exact (div_eq_zero_iff.mp hz).resolve_right hden
  · intro hp
    rw [hp,zero_div] at hres
    linarith

theorem Thioredoxin.pool_iff (S : Thioredoxin) (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    y+S.baseline+tFlux S.a S.b S.c S.d S.e S.E y/(S.k*x)=S.total ↔
    S.branch.a*y^2+(S.branch.b+S.branch.c/x)*y-S.branch.d=0 := by
  have hden : 1+y*S.e*tRho S.a S.b S.c S.d ≠ 0 := by
    have h := mul_pos (mul_pos hy S.he) S.rho_pos
    linarith
  have hres := t_pool_residual S.a S.b S.c S.d S.e S.E S.total S.baseline S.k x y
    (ne_of_gt S.hk) (ne_of_gt hx) hden
  change _ ↔ tPoly S.a S.b S.c S.d S.e S.E S.total S.baseline S.k x y=0
  constructor
  · intro hp
    have hz : tPoly S.a S.b S.c S.d S.e S.E S.total S.baseline S.k x y/
        (1+y*S.e*tRho S.a S.b S.c S.d)=0 := by linarith
    exact (div_eq_zero_iff.mp hz).resolve_right hden
  · intro hp
    rw [hp,zero_div] at hres
    linarith

/-- Actual private carrier pools, with all enzyme states recovered by the
source reconstruction lemmas, and one shared NADPH source/current balance. -/
def PoolJoint (G : Glutathione) (T : Thioredoxin) (s V N D qG qT : ℝ) : Prop :=
  ∃ x g t : ℝ, 0<x ∧ x≤N ∧ 0<g ∧ 0<t ∧
    g+2*(G.baseline+gFlux G.a G.b G.c G.E g/(G.k*x))+
      gFlux G.a G.b G.c G.E g/(G.c*g)=G.total ∧
    t+T.baseline+tFlux T.a T.b T.c T.d T.e T.E t/(T.k*x)=T.total ∧
    MaintainedSource.supply s V N D x=
      gFlux G.a G.b G.c G.E g+tFlux T.a T.b T.c T.d T.e T.E t ∧
    qG≤gFlux G.a G.b G.c G.E g ∧ qT≤tFlux T.a T.b T.c T.d T.e T.E t

theorem pool_joint_iff_source_joint (G : Glutathione) (T : Thioredoxin)
    (s V N D qG qT : ℝ) :
    PoolJoint G T s V N D qG qT ↔ SourceJoint G.branch T.branch s V N D qG qT := by
  constructor
  · rintro ⟨x,g,t,hx,hN,hg,ht,hgp,htp,hbal,hqg,hqt⟩
    refine ⟨x,g,t,hx,hN,hg,ht,(G.pool_iff x g hx hg).mp hgp,
      (T.pool_iff x t hx ht).mp htp,?_,?_,?_⟩
    · simpa only [G.rate_eq,T.rate_eq] using hbal
    · simpa only [G.rate_eq] using hqg
    · simpa only [T.rate_eq] using hqt
  · rintro ⟨x,g,t,hx,hN,hg,ht,hgp,htp,hbal,hqg,hqt⟩
    refine ⟨x,g,t,hx,hN,hg,ht,(G.pool_iff x g hx hg).mpr hgp,
      (T.pool_iff x t hx ht).mpr htp,?_,?_,?_⟩
    · simpa only [G.rate_eq,T.rate_eq] using hbal
    · simpa only [G.rate_eq] using hqg
    · simpa only [T.rate_eq] using hqt

theorem pool_joint_iff_repair (G : Glutathione) (T : Thioredoxin)
    (s V N D qG qT : ℝ) (hs : 0<s) (hV : 0<V) (hND : N<D)
    (hqG : 0<qG) (hqT : 0<qT)
    (hcapG : 0<G.branch.p-qG*G.branch.v) (hcapT : 0<T.branch.p-qT*T.branch.v)
    (hmG : 0<G.branch.margin qG) (hmT : 0<T.branch.margin qT)
    (hLN : max (G.branch.floor qG) (T.branch.floor qT)<N) :
    PoolJoint G T s V N D qG qT ↔
      minimumScale G.branch T.branch V N D (max (G.branch.floor qG) (T.branch.floor qT))≤s :=
  (pool_joint_iff_source_joint G T s V N D qG qT).trans
    (source_joint_iff_repair G.branch T.branch s V N D qG qT hs hV hND
      hqG hqT hcapG hcapT hmG hmT hLN)

end
end CommonEnvironmentProtection.SourceFamilies
