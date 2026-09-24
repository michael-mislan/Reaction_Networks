import proofs.CommonEnvironmentProtection.Allocation

/-! Complements to the root theorem: uniqueness of the full literal joint
steady state, and the finite-source ceiling equivalence (a finite regeneration
scale admits joint service iff each quota is strictly below its branch ceiling
current at x = N). Both were previously argued only conventionally. -/
namespace CommonEnvironmentProtection.Complement
noncomputable section
open CoupledPrivate SourceFamilies LiteralSteady PrivateBranches QuadraticPool SourceExample

attribute [ext] GState TState

/-- Strict version of the positive-root sign characterization. -/
theorem polynomial_lt_iff (a b d y : ℝ) (ha : 0 < a) (hd : 0 < d) (hy : 0 ≤ y) :
    a*y^2+b*y-d < 0 ↔ y < root a b d := by
  have hz := root_pos a b d ha hd
  have hb := root_balance a b d ha hd
  have hp := factor_positive a b d y (root a b d) ha hd hy hz hb
  have he : a*y^2+b*y-d = (y-root a b d)*(a*(y+root a b d)+b) := by
    linear_combination hb
  rw [he]
  constructor
  · intro h
    by_contra! hh
    have := mul_nonneg (sub_nonneg.mpr hh) hp.le
    linarith
  · intro h
    exact mul_neg_of_neg_of_pos (sub_neg.mpr h) hp

/-- A quota strictly below the branch ceiling current j(N) satisfies every
threshold-inversion hypothesis, and its NADPH floor lies strictly below N. -/
theorem ceiling_admits (B : Branch) (q N : ℝ) (hq : 0 < q) (hN : 0 < N)
    (h : q < B.flux N) :
    0 < B.p-q*B.v ∧ 0 < B.margin q ∧ B.floor q < N := by
  have hypos : 0 < B.carrier N := B.carrier_pos N
  have hden : 0 < B.u+B.v*B.carrier N := by nlinarith [B.hu, mul_nonneg B.hv hypos.le]
  have h1 : q < B.p*B.carrier N/(B.u+B.v*B.carrier N) := h
  have hlt : q*(B.u+B.v*B.carrier N) < B.p*B.carrier N := (lt_div_iff₀ hden).mp h1
  have hcap : 0 < B.p-q*B.v := by
    by_contra! hc
    nlinarith [mul_nonneg (neg_nonneg.mpr hc) hypos.le, mul_pos hq B.hu]
  have hY : B.target q < B.carrier N := by
    unfold Branch.target
    rw [div_lt_iff₀ hcap]
    nlinarith
  have hYpos : 0 < B.target q := B.target_pos q hq hcap
  have hpoly : B.a*(B.target q)^2+(B.b+B.c/N)*B.target q-B.d < 0 :=
    (polynomial_lt_iff B.a (B.b+B.c/N) B.d (B.target q) B.ha B.hd hYpos.le).mpr hY
  have hsplit : (B.b+B.c/N)*B.target q = B.b*B.target q+B.c*B.target q/N := by ring
  have hcN : 0 < B.c*B.target q/N := div_pos (mul_pos B.hc hYpos) hN
  have h2 : B.c*B.target q/N < B.margin q := by
    unfold Branch.margin
    linarith
  have hm : 0 < B.margin q := hcN.trans h2
  refine ⟨hcap, hm, ?_⟩
  unfold Branch.floor
  rw [div_lt_iff₀ hm]
  rw [div_lt_iff₀ hN] at h2
  linarith

/-- Every joint witness has its carriers on the response curve, its currents on
the flux curve, NADPH at or above the binding floor, and zero shared residual. -/
theorem witness_data (G : Glutathione) (T : Thioredoxin) (s V N D qG qT x : ℝ)
    (g : GState) (t : TState) (hqG : 0<qG) (hqT : 0<qT)
    (hcapG : 0<G.branch.p-qG*G.branch.v) (hcapT : 0<T.branch.p-qT*T.branch.v)
    (hmG : 0<G.branch.margin qG) (hmT : 0<T.branch.margin qT)
    (hx : 0<x) (hg : g.Steady G x) (ht : t.Steady T x)
    (hbal : MaintainedSource.supply s V N D x=g.j+t.j) (hqg : qG≤g.j) (hqt : qT≤t.j) :
    g.g=G.branch.carrier x ∧ t.y=T.branch.carrier x ∧
    g.j=G.branch.flux x ∧ t.j=T.branch.flux x ∧
    max (G.branch.floor qG) (T.branch.floor qT) ≤ x ∧
    CoupledPrivate.residual G.branch T.branch s V N D x = 0 := by
  obtain ⟨eg,pg⟩ := g.eliminate G x hx hg
  obtain ⟨et,pt⟩ := t.eliminate T x hx ht
  have hge : g.g = G.branch.carrier x :=
    positive_root_unique _ _ _ _ G.branch.ha G.branch.hd hg.1 ((G.pool_iff x g.g hx hg.1).mp pg)
  have hte : t.y = T.branch.carrier x :=
    positive_root_unique _ _ _ _ T.branch.ha T.branch.hd ht.1 ((T.pool_iff x t.y hx ht.1).mp pt)
  have ejg : g.j = G.branch.flux x := by rw [eg,hge,← G.rate_eq]; rfl
  have ejt : t.j = T.branch.flux x := by rw [et,hte,← T.rate_eq]; rfl
  refine ⟨hge,hte,ejg,ejt,?_,?_⟩
  · exact max_le ((G.branch.service_iff qG x hqG hx hcapG hmG).mp (by rw [← ejg]; exact hqg))
      ((T.branch.service_iff qT x hqT hx hcapT hmT).mp (by rw [← ejt]; exact hqt))
  · unfold CoupledPrivate.residual
    rw [hbal,ejg,ejt]
    ring

theorem residual_strictAnti (G T : Branch) (s V N D L : ℝ)
    (hs : 0<s) (hV : 0<V) (hL : 0<L) (hND : N<D) :
    StrictAntiOn (CoupledPrivate.residual G T s V N D) (Set.Icc L N) := by
  intro x hx y hy hxy
  have hsup := MaintainedSource.drift_strictAnti s V N D 0 0 hs hV hND (le_refl 0) hx.2 hy.2 hxy
  simp only [MaintainedSource.drift, zero_mul, sub_zero] at hsup
  have hxp : 0 < x := hL.trans_le hx.1
  have hyp : 0 < y := hL.trans_le hy.1
  have hg := G.flux_strictMono hxp hyp hxy
  have ht := T.flux_strictMono hxp hyp hxy
  unfold CoupledPrivate.residual
  linarith

/-- Uniqueness of the full literal joint steady state: any two quota-satisfying
witnesses share the NADPH concentration and every private enzyme/carrier value. -/
theorem joint_state_unique (G : Glutathione) (T : Thioredoxin) (s V N D qG qT : ℝ)
    (hs : 0<s) (hV : 0<V) (hND : N<D) (hqG : 0<qG) (hqT : 0<qT)
    (hcapG : 0<G.branch.p-qG*G.branch.v) (hcapT : 0<T.branch.p-qT*T.branch.v)
    (hmG : 0<G.branch.margin qG) (hmT : 0<T.branch.margin qT)
    (x x' : ℝ) (g g' : GState) (t t' : TState)
    (h : 0<x ∧ x≤N ∧ g.Steady G x ∧ t.Steady T x ∧
      MaintainedSource.supply s V N D x=g.j+t.j ∧ qG≤g.j ∧ qT≤t.j)
    (h' : 0<x' ∧ x'≤N ∧ g'.Steady G x' ∧ t'.Steady T x' ∧
      MaintainedSource.supply s V N D x'=g'.j+t'.j ∧ qG≤g'.j ∧ qT≤t'.j) :
    x=x' ∧ g=g' ∧ t=t' := by
  obtain ⟨hx,hxN,hg,ht,hbal,hqg,hqt⟩ := h
  obtain ⟨hx',hxN',hg',ht',hbal',hqg',hqt'⟩ := h'
  obtain ⟨hge,hte,ejg,ejt,hL,hres⟩ :=
    witness_data G T s V N D qG qT x g t hqG hqT hcapG hcapT hmG hmT hx hg ht hbal hqg hqt
  obtain ⟨hge',hte',ejg',ejt',hL',hres'⟩ :=
    witness_data G T s V N D qG qT x' g' t' hqG hqT hcapG hcapT hmG hmT hx' hg' ht' hbal' hqg' hqt'
  have hLpos : 0 < max (G.branch.floor qG) (T.branch.floor qT) :=
    (G.branch.floor_pos qG hqG hcapG hmG).trans_le (le_max_left _ _)
  have hxx : x = x' :=
    (residual_strictAnti G.branch T.branch s V N D _ hs hV hLpos hND).injOn
      ⟨hL,hxN⟩ ⟨hL',hxN'⟩ (hres.trans hres'.symm)
  subst hxx
  refine ⟨rfl,?_,?_⟩
  · obtain ⟨hg1,_,_,_,_,_,_,hr,ho,hb,hz⟩ := hg
    obtain ⟨_,_,_,_,_,_,_,hr',ho',hb',hz'⟩ := hg'
    have egg : g.g = g'.g := hge.trans hge'.symm
    have ejj : g.j = g'.j := ejg.trans ejg'.symm
    rw [← egg] at ho' hb'
    have hk : G.k*x ≠ 0 := ne_of_gt (mul_pos G.hk hx)
    have ez := mul_left_cancel₀ hk (hz.trans (ejj.trans hz'.symm))
    have er := mul_left_cancel₀ (ne_of_gt G.ha) (hr.trans (ejj.trans hr'.symm))
    have eo := mul_left_cancel₀ (ne_of_gt (mul_pos G.hb hg1)) (ho.trans (ejj.trans ho'.symm))
    have eb := mul_left_cancel₀ (ne_of_gt (mul_pos G.hc hg1)) (hb.trans (ejj.trans hb'.symm))
    ext
    · exact egg
    · linarith
    · exact er
    · exact eo
    · exact eb
    · exact ejj
  · obtain ⟨ht1,_,_,_,_,_,_,hT,hr,hh,hw,hv,hz⟩ := ht
    obtain ⟨_,_,_,_,_,_,_,hT',hr',hh',hw',hv',hz'⟩ := ht'
    have eyy : t.y = t'.y := hte.trans hte'.symm
    have ejj : t.j = t'.j := ejt.trans ejt'.symm
    rw [← eyy] at hv' hT'
    have hk : T.k*x ≠ 0 := ne_of_gt (mul_pos T.hk hx)
    have ez := mul_left_cancel₀ hk (hz.trans (ejj.trans hz'.symm))
    have er := mul_left_cancel₀ (ne_of_gt T.ha) (hr.trans (ejj.trans hr'.symm))
    have eh := mul_left_cancel₀ (ne_of_gt T.hd) (hh.trans (ejj.trans hh'.symm))
    have ew : t.w = t'.w := by
      apply mul_left_cancel₀ (ne_of_gt T.hc)
      rw [hw,hw',eh]
    have ev := mul_left_cancel₀ (ne_of_gt (mul_pos T.he ht1)) (hv.trans (ejj.trans hv'.symm))
    ext
    · exact eyy
    · linarith
    · exact er
    · exact eh
    · exact ew
    · exact ev
    · exact ejj

/-- Finite-source ceiling equivalence: some positive regeneration scale admits
joint literal service iff each quota is strictly below its branch ceiling. -/
theorem finite_repair_iff (G : Glutathione) (T : Thioredoxin) (V N D qG qT : ℝ)
    (hV : 0<V) (hN : 0<N) (hND : N<D) (hqG : 0<qG) (hqT : 0<qT) :
    (∃ s : ℝ, 0<s ∧ FullJoint G T s V N D qG qT) ↔
      qG < G.branch.flux N ∧ qT < T.branch.flux N := by
  constructor
  · rintro ⟨s,_,x,g,t,hx,hxN,hg,ht,hbal,hqg,hqt⟩
    obtain ⟨eg,pg⟩ := g.eliminate G x hx hg
    obtain ⟨et,pt⟩ := t.eliminate T x hx ht
    have hge : g.g = G.branch.carrier x :=
      positive_root_unique _ _ _ _ G.branch.ha G.branch.hd hg.1 ((G.pool_iff x g.g hx hg.1).mp pg)
    have hte : t.y = T.branch.carrier x :=
      positive_root_unique _ _ _ _ T.branch.ha T.branch.hd ht.1 ((T.pool_iff x t.y hx ht.1).mp pt)
    have ejg : g.j = G.branch.flux x := by rw [eg,hge,← G.rate_eq]; rfl
    have ejt : t.j = T.branch.flux x := by rw [et,hte,← T.rate_eq]; rfl
    have hxlt : x < N := by
      rcases lt_or_eq_of_le hxN with hlt | heq
      · exact hlt
      · exfalso
        have hzero : MaintainedSource.supply s V N D N = 0 := by
          simp [MaintainedSource.supply]
        rw [heq] at hbal ejg ejt
        have hjg := G.branch.flux_pos N
        have hjt := T.branch.flux_pos N
        linarith
    constructor
    · calc qG ≤ g.j := hqg
        _ = G.branch.flux x := ejg
        _ < G.branch.flux N := G.branch.flux_strictMono hx (hx.trans hxlt) hxlt
    · calc qT ≤ t.j := hqt
        _ = T.branch.flux x := ejt
        _ < T.branch.flux N := T.branch.flux_strictMono hx (hx.trans hxlt) hxlt
  · rintro ⟨hG,hT⟩
    obtain ⟨hcapG,hmG,hfG⟩ := ceiling_admits G.branch qG N hqG hN hG
    obtain ⟨hcapT,hmT,hfT⟩ := ceiling_admits T.branch qT N hqT hN hT
    have hLN : max (G.branch.floor qG) (T.branch.floor qT) < N := max_lt hfG hfT
    have hL : 0 < max (G.branch.floor qG) (T.branch.floor qT) :=
      (G.branch.floor_pos qG hqG hcapG hmG).trans_le (le_max_left _ _)
    have hsup : 0 < MaintainedSource.supply 1 V N D (max (G.branch.floor qG) (T.branch.floor qT)) := by
      unfold MaintainedSource.supply
      exact div_pos (mul_pos (mul_pos (by norm_num) hV) (sub_pos.mpr hLN)) (by linarith)
    have hsm : 0 < minimumScale G.branch T.branch V N D
        (max (G.branch.floor qG) (T.branch.floor qT)) :=
      div_pos (add_pos (G.branch.flux_pos _) (T.branch.flux_pos _)) hsup
    exact ⟨_, hsm, (jointProtection_iff_minimumRegeneration G T _ V N D qG qT hsm hV hND
      hqG hqT hcapG hcapT hmG hmT hLN).mpr le_rfl⟩

/-- Nominal instance: both declared quotas lie strictly below their ceilings,
so a finite repair exists (the certified one), and both ceiling currents are
enclosed by explicit rationals. -/
theorem nominal_quotas_below_ceilings :
    10 < glutathione.branch.flux 30 ∧ 4 < thioredoxin.branch.flux 30 :=
  (finite_repair_iff glutathione thioredoxin 375 30 (873/10) 10 4
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mp
    ⟨11371268/100000000, by norm_num, source_certified_repair⟩

end
end CommonEnvironmentProtection.Complement
