import proofs.CommonEnvironmentProtection.SourceFamilies

namespace CommonEnvironmentProtection.LiteralSteady
noncomputable section
open SourceFamilies PrivateBranches CoupledPrivate

structure GState where
  g : ℝ
  z : ℝ
  r : ℝ
  o : ℝ
  bound : ℝ
  j : ℝ

def GState.Steady (s : GState) (S : Glutathione) (x : ℝ) : Prop :=
  0<s.g ∧ 0<s.z ∧ 0<s.r ∧ 0<s.o ∧ 0<s.bound ∧
  s.r+s.o+s.bound=S.E ∧ s.g+2*s.z+s.bound=S.total ∧
  S.a*s.r=s.j ∧ S.b*s.g*s.o=s.j ∧ S.c*s.g*s.bound=s.j ∧
  S.k*x*(s.z-S.baseline)=s.j

structure TState where
  y : ℝ
  z : ℝ
  r : ℝ
  h : ℝ
  w : ℝ
  v : ℝ
  j : ℝ

def TState.Steady (s : TState) (S : Thioredoxin) (x : ℝ) : Prop :=
  0<s.y ∧ 0<s.z ∧ 0<s.r ∧ 0<s.h ∧ 0≤s.w ∧ 0<s.v ∧
  s.r+s.h+s.w+s.v=S.E ∧ s.y+s.z=S.total ∧
  S.a*s.r=s.j ∧ S.d*s.h=s.j ∧ S.c*s.w=S.b*s.h ∧ S.e*s.y*s.v=s.j ∧
  S.k*x*(s.z-S.baseline)=s.j

theorem GState.eliminate (s : GState) (S : Glutathione) (x : ℝ)
    (hx : 0<x) (h : s.Steady S x) :
    s.j=gFlux S.a S.b S.c S.E s.g ∧
    s.g+2*(S.baseline+gFlux S.a S.b S.c S.E s.g/(S.k*x))+
      gFlux S.a S.b S.c S.E s.g/(S.c*s.g)=S.total := by
  rcases h with ⟨hg,_,_,_,_,hE,hG,hr,ho,hb,hz⟩
  have er : s.r=s.j/S.a := (eq_div_iff (ne_of_gt S.ha)).mpr (by nlinarith)
  have eo : s.o=s.j/(S.b*s.g) :=
    (eq_div_iff (ne_of_gt (mul_pos S.hb hg))).mpr (by nlinarith)
  have eb : s.bound=s.j/(S.c*s.g) :=
    (eq_div_iff (ne_of_gt (mul_pos S.hc hg))).mpr (by nlinarith)
  have ez : s.z=S.baseline+s.j/(S.k*x) := by
    have he : s.j/(S.k*x)=s.z-S.baseline :=
      (div_eq_iff (ne_of_gt (mul_pos S.hk hx))).mpr (by nlinarith)
    linarith
  rw [er,eo,eb] at hE
  let R := 1/S.a+1/(S.b*s.g)+1/(S.c*s.g)
  have hR : 0<R := by
    exact add_pos (add_pos (one_div_pos.mpr S.ha) (one_div_pos.mpr (mul_pos S.hb hg)))
      (one_div_pos.mpr (mul_pos S.hc hg))
  have hj : s.j*R=S.E := by dsimp [R]; convert hE using 1; ring
  have hf := g_enzyme_pool S.a S.b S.c S.E s.g S.ha S.hb S.hc hg
  have hfj : gFlux S.a S.b S.c S.E s.g*R=S.E := by
    dsimp [R]; convert hf using 1; ring
  have heq : (s.j-gFlux S.a S.b S.c S.E s.g)*R=0 := by nlinarith
  have ej := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right (ne_of_gt hR))
  refine ⟨ej,?_⟩
  simpa only [ez,eb,ej] using hG

theorem TState.eliminate (s : TState) (S : Thioredoxin) (x : ℝ)
    (hx : 0<x) (h : s.Steady S x) :
    s.j=tFlux S.a S.b S.c S.d S.e S.E s.y ∧
    s.y+S.baseline+tFlux S.a S.b S.c S.d S.e S.E s.y/(S.k*x)=S.total := by
  rcases h with ⟨hy,_,_,_,_,_,hE,hT,hr,hh,hw,hv,hz⟩
  have er : s.r=s.j/S.a := (eq_div_iff (ne_of_gt S.ha)).mpr (by nlinarith)
  have eh : s.h=s.j/S.d := (eq_div_iff (ne_of_gt S.hd)).mpr (by nlinarith)
  have ew : s.w=S.b*s.j/(S.c*S.d) := by
    apply (eq_div_iff (ne_of_gt (mul_pos S.hc S.hd))).mpr
    nlinarith [congrArg (fun z => z*S.d) hw,congrArg (fun z => S.b*z) hh]
  have ev : s.v=s.j/(S.e*s.y) :=
    (eq_div_iff (ne_of_gt (mul_pos S.he hy))).mpr (by nlinarith)
  have ez : s.z=S.baseline+s.j/(S.k*x) := by
    have he : s.j/(S.k*x)=s.z-S.baseline :=
      (div_eq_iff (ne_of_gt (mul_pos S.hk hx))).mpr (by nlinarith)
    linarith
  rw [er,eh,ew,ev] at hE
  let R := tRho S.a S.b S.c S.d+1/(S.e*s.y)
  have hR : 0<R := add_pos S.rho_pos (one_div_pos.mpr (mul_pos S.he hy))
  have hj : s.j*R=S.E := by dsimp [R,tRho]; convert hE using 1; ring
  have hden : 1+s.y*S.e*tRho S.a S.b S.c S.d≠0 := by
    have hp := mul_pos (mul_pos hy S.he) S.rho_pos
    linarith
  have hf := t_enzyme_pool S.a S.b S.c S.d S.e S.E s.y
    (ne_of_gt S.he) (ne_of_gt hy) hden
  have hfj : tFlux S.a S.b S.c S.d S.e S.E s.y*R=S.E := by
    dsimp [R,tRho]; convert hf using 1; ring
  have heq : (s.j-tFlux S.a S.b S.c S.d S.e S.E s.y)*R=0 := by nlinarith
  have ej := sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_right (ne_of_gt hR))
  refine ⟨ej,?_⟩
  rw [ez,ej] at hT
  linarith

def reconstructG (S : Glutathione) (x g : ℝ) : GState :=
  let j := gFlux S.a S.b S.c S.E g
  ⟨g,S.baseline+j/(S.k*x),j/S.a,j/(S.b*g),j/(S.c*g),j⟩

def reconstructT (S : Thioredoxin) (x y : ℝ) : TState :=
  let j := tFlux S.a S.b S.c S.d S.e S.E y
  ⟨y,S.baseline+j/(S.k*x),j/S.a,j/S.d,S.b*j/(S.c*S.d),j/(S.e*y),j⟩

theorem reconstructG_steady (S : Glutathione) (x g : ℝ) (hx : 0<x) (hg : 0<g)
    (hpool : g+2*(S.baseline+gFlux S.a S.b S.c S.E g/(S.k*x))+
      gFlux S.a S.b S.c S.E g/(S.c*g)=S.total) :
    (reconstructG S x g).Steady S x := by
  have hr := g_rho_pos _ _ _ S.ha S.hb S.hc
  have hj : 0<gFlux S.a S.b S.c S.E g :=
    div_pos (mul_pos (mul_pos S.hE S.ha) hg) (add_pos hg hr)
  refine ⟨hg,add_pos_of_nonneg_of_pos S.hbaseline (div_pos hj (mul_pos S.hk hx)),
    div_pos hj S.ha,div_pos hj (mul_pos S.hb hg),div_pos hj (mul_pos S.hc hg),
    g_enzyme_pool _ _ _ _ _ S.ha S.hb S.hc hg,hpool,?_,?_,?_,?_⟩
  all_goals dsimp [reconstructG]
  all_goals field_simp [ne_of_gt S.ha,ne_of_gt S.hb,ne_of_gt S.hc,ne_of_gt S.hk]
  all_goals ring

theorem reconstructT_steady (S : Thioredoxin) (x y : ℝ) (hx : 0<x) (hy : 0<y)
    (hpool : y+S.baseline+tFlux S.a S.b S.c S.d S.e S.E y/(S.k*x)=S.total) :
    (reconstructT S x y).Steady S x := by
  have hdenpos : 0<1+y*S.e*tRho S.a S.b S.c S.d := by
    have hp := mul_pos (mul_pos hy S.he) S.rho_pos
    linarith
  have hj : 0<tFlux S.a S.b S.c S.d S.e S.E y :=
    div_pos (mul_pos (mul_pos S.hE S.he) hy) hdenpos
  refine ⟨hy,add_pos_of_nonneg_of_pos S.hbaseline (div_pos hj (mul_pos S.hk hx)),
    div_pos hj S.ha,div_pos hj S.hd,div_nonneg (mul_nonneg S.hb hj.le) (mul_pos S.hc S.hd).le,
    div_pos hj (mul_pos S.he hy),
    t_enzyme_pool _ _ _ _ _ _ _ (ne_of_gt S.he) (ne_of_gt hy) (ne_of_gt hdenpos),
    by dsimp [reconstructT]; linarith,?_,?_,?_,?_,?_⟩
  all_goals dsimp [reconstructT]
  all_goals field_simp [ne_of_gt S.ha,ne_of_gt S.hc,ne_of_gt S.hd,ne_of_gt S.he,ne_of_gt S.hk]
  all_goals ring

def FullJoint (G : Glutathione) (T : Thioredoxin) (s V N D qG qT : ℝ) : Prop :=
  ∃ (x : ℝ) (g : GState) (t : TState), 0<x ∧ x≤N ∧ g.Steady G x ∧ t.Steady T x ∧
    MaintainedSource.supply s V N D x=g.j+t.j ∧ qG≤g.j ∧ qT≤t.j

theorem full_joint_iff_pool (G : Glutathione) (T : Thioredoxin) (s V N D qG qT : ℝ) :
    FullJoint G T s V N D qG qT ↔ PoolJoint G T s V N D qG qT := by
  constructor
  · rintro ⟨x,g,t,hx,hN,hg,ht,hbal,hqg,hqt⟩
    obtain ⟨eg,pg⟩ := g.eliminate G x hx hg
    obtain ⟨et,pt⟩ := t.eliminate T x hx ht
    exact ⟨x,g.g,t.y,hx,hN,hg.1,ht.1,pg,pt,by simpa only [eg,et] using hbal,
      by simpa only [eg] using hqg,by simpa only [et] using hqt⟩
  · rintro ⟨x,g,t,hx,hN,hg,ht,pg,pt,hbal,hqg,hqt⟩
    exact ⟨x,reconstructG G x g,reconstructT T x t,hx,hN,
      reconstructG_steady G x g hx hg pg,reconstructT_steady T x t hx ht pt,hbal,hqg,hqt⟩

end
end CommonEnvironmentProtection.LiteralSteady
