import proofs.CommonEnvironmentProtection.QuadraticPool
import proofs.CommonEnvironmentProtection.MaintainedSource

namespace CommonEnvironmentProtection.CoupledPrivate
noncomputable section
open QuadraticPool

structure Branch where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  p : ℝ
  u : ℝ
  v : ℝ
  ha : 0 < a
  hc : 0 < c
  hd : 0 < d
  hp : 0 < p
  hu : 0 < u
  hv : 0 ≤ v

def Branch.carrier (B : Branch) (x : ℝ) := response B.a B.b B.c B.d x
def Branch.flux (B : Branch) (x : ℝ) := rate B.p B.u B.v (B.carrier x)
def Branch.target (B : Branch) (q : ℝ) := q*B.u/(B.p-q*B.v)
def Branch.margin (B : Branch) (q : ℝ) :=
  B.d-B.a*(B.target q)^2-B.b*B.target q
def Branch.floor (B : Branch) (q : ℝ) := B.c*B.target q/B.margin q

theorem Branch.carrier_pos (B : Branch) (x : ℝ) : 0 < B.carrier x :=
  root_pos _ _ _ B.ha B.hd

theorem Branch.flux_pos (B : Branch) (x : ℝ) : 0 < B.flux x := by
  have hy := B.carrier_pos x
  exact div_pos (mul_pos B.hp hy) (by nlinarith [B.hu, mul_nonneg B.hv hy.le])

theorem Branch.flux_strictMono (B : Branch) : StrictMonoOn B.flux (Set.Ioi 0) := by
  intro x hx z hz h
  apply rate_strictMono _ _ _ B.hp B.hu B.hv (B.carrier_pos x).le (B.carrier_pos z).le
  exact response_strictMono _ _ _ _ B.ha B.hc B.hd hx hz h

theorem Branch.flux_continuous (B : Branch) (L U : ℝ) (hL : 0 < L) :
    ContinuousOn B.flux (Set.Icc L U) := by
  have hy : ContinuousOn B.carrier (Set.Icc L U) := response_continuous _ _ _ _ _ _ hL
  have hn : ∀ x ∈ Set.Icc L U, B.u+B.v*B.carrier x ≠ 0 := by
    intro x _
    have hp := B.carrier_pos x
    have hm := mul_nonneg B.hv hp.le
    have hu := B.hu
    linarith
  exact (continuousOn_const.mul hy).div
    (continuousOn_const.add (continuousOn_const.mul hy)) hn

theorem Branch.target_pos (B : Branch) (q : ℝ) (hq : 0 < q)
    (hcap : 0 < B.p-q*B.v) : 0 < B.target q :=
  div_pos (mul_pos hq B.hu) hcap

theorem Branch.floor_pos (B : Branch) (q : ℝ) (hq : 0 < q)
    (hcap : 0 < B.p-q*B.v) (hm : 0 < B.margin q) : 0 < B.floor q :=
  div_pos (mul_pos B.hc (B.target_pos q hq hcap)) hm

theorem Branch.service_iff (B : Branch) (q x : ℝ) (hq : 0 < q) (hx : 0 < x)
    (hcap : 0 < B.p-q*B.v) (hm : 0 < B.margin q) :
    q ≤ B.flux x ↔ B.floor q ≤ x := by
  exact (rate_service_iff _ _ _ _ _ B.hu B.hv (B.carrier_pos x).le hcap).trans
    (response_threshold_iff _ _ _ _ _ _ B.ha B.hd hx (B.target_pos q hq hcap).le hm)

def residual (G T : Branch) (s V N D x : ℝ) :=
  MaintainedSource.supply s V N D x-G.flux x-T.flux x

def minimumScale (G T : Branch) (V N D L : ℝ) :=
  (G.flux L+T.flux L)/MaintainedSource.supply 1 V N D L

theorem unique_safe_iff (G T : Branch) (s V N D L : ℝ)
    (hs : 0 < s) (hV : 0 < V) (hL : 0 < L) (hLN : L < N) (hND : N < D) :
    (∃! x, x ∈ Set.Icc L N ∧ residual G T s V N D x = 0) ↔
      minimumScale G T V N D L ≤ s := by
  have hc : ContinuousOn (residual G T s V N D) (Set.Icc L N) := by
    have h := MaintainedSource.drift_continuous s V N D 0 0 L N hND le_rfl
    change ContinuousOn (fun x => MaintainedSource.supply s V N D x-0*x-0) (Set.Icc L N) at h
    simp only [zero_mul, sub_zero] at h
    exact (h.sub (G.flux_continuous L N hL)).sub (T.flux_continuous L N hL)
  have ha : StrictAntiOn (residual G T s V N D) (Set.Icc L N) := by
    intro x hx y hy hxy
    have hsup := MaintainedSource.drift_strictAnti s V N D 0 0 hs hV hND
      (le_refl 0) hx.2 hy.2 hxy
    simp only [MaintainedSource.drift, zero_mul, sub_zero] at hsup
    have hxp : 0 < x := hL.trans_le hx.1
    have hyp : 0 < y := hL.trans_le hy.1
    have hg := G.flux_strictMono hxp hyp hxy
    have ht := T.flux_strictMono hxp hyp hxy
    unfold residual
    linarith
  rw [CommonEnvironmentProtection.safe_equilibrium_iff _ _ _ hLN.le hc ha]
  have hu : residual G T s V N D N ≤ 0 := by
    have hg := G.flux_pos N
    have ht := T.flux_pos N
    unfold residual MaintainedSource.supply
    simp only [sub_self,mul_zero,zero_div]
    linarith
  rw [and_iff_left hu]
  have hb : 0 < MaintainedSource.supply 1 V N D L := by
    unfold MaintainedSource.supply
    exact div_pos (mul_pos (mul_pos (by norm_num) hV) (sub_pos.mpr hLN)) (by linarith)
  have hscale : MaintainedSource.supply s V N D L =
      s*MaintainedSource.supply 1 V N D L := by unfold MaintainedSource.supply; ring
  unfold minimumScale residual
  rw [div_le_iff₀ hb,hscale]
  constructor <;> intro h <;> linarith

def SourceJoint (G T : Branch) (s V N D qG qT : ℝ) : Prop :=
  ∃ x g t : ℝ, 0 < x ∧ x ≤ N ∧ 0 < g ∧ 0 < t ∧
    G.a*g^2+(G.b+G.c/x)*g-G.d=0 ∧
    T.a*t^2+(T.b+T.c/x)*t-T.d=0 ∧
    MaintainedSource.supply s V N D x=rate G.p G.u G.v g+rate T.p T.u T.v t ∧
    qG ≤ rate G.p G.u G.v g ∧ qT ≤ rate T.p T.u T.v t

/-- Full private-state polynomial system and shared source balance, with
positive reconstructed carriers, iff the exact minimum repair inequality. -/
theorem source_joint_iff_repair (G T : Branch) (s V N D qG qT : ℝ)
    (hs : 0 < s) (hV : 0 < V) (hND : N < D)
    (hqG : 0 < qG) (hqT : 0 < qT)
    (hcapG : 0 < G.p-qG*G.v) (hcapT : 0 < T.p-qT*T.v)
    (hmG : 0 < G.margin qG) (hmT : 0 < T.margin qT)
    (hLN : max (G.floor qG) (T.floor qT) < N) :
    SourceJoint G T s V N D qG qT ↔
      minimumScale G T V N D (max (G.floor qG) (T.floor qT)) ≤ s := by
  let L := max (G.floor qG) (T.floor qT)
  have hL : 0 < L := (G.floor_pos qG hqG hcapG hmG).trans_le (le_max_left _ _)
  rw [← unique_safe_iff G T s V N D L hs hV hL hLN hND]
  constructor
  · rintro ⟨x,g,t,hx,hxN,hg,ht,hgb,htb,hbal,hqg,hqt⟩
    have hge : g=G.carrier x := positive_root_unique _ _ _ _ G.ha G.hd hg hgb
    have hte : t=T.carrier x := positive_root_unique _ _ _ _ T.ha T.hd ht htb
    subst g
    subst t
    have hxL : L ≤ x := max_le ((G.service_iff qG x hqG hx hcapG hmG).mp hqg)
      ((T.service_iff qT x hqT hx hcapT hmT).mp hqt)
    have hres : residual G T s V N D x=0 := by
      unfold residual Branch.flux
      linarith
    have hsign : minimumScale G T V N D L ≤ s := by
      by_contra! hno
      have hbase : 0 < MaintainedSource.supply 1 V N D L := by
        unfold MaintainedSource.supply
        exact div_pos (mul_pos (mul_pos (by norm_num) hV) (sub_pos.mpr hLN)) (by linarith)
      have hbad : residual G T s V N D L < 0 := by
        unfold minimumScale at hno
        have hh := (lt_div_iff₀ hbase).mp hno
        have he : MaintainedSource.supply s V N D L =
            s*MaintainedSource.supply 1 V N D L := by unfold MaintainedSource.supply; ring
        unfold residual
        rw [he]
        linarith
      have hsup := (MaintainedSource.drift_strictAnti s V N D 0 0 hs hV hND
        (le_refl 0)).antitoneOn (show L ≤ N from hLN.le) hxN hxL
      simp only [MaintainedSource.drift,zero_mul,sub_zero] at hsup
      have hgf := G.flux_strictMono.monotoneOn hL hx hxL
      have htf := T.flux_strictMono.monotoneOn hL hx hxL
      unfold residual at hbad hres
      linarith
    exact (unique_safe_iff G T s V N D L hs hV hL hLN hND).mpr hsign
  · rintro ⟨x,⟨hx,hres⟩,_⟩
    have hxp : 0 < x := hL.trans_le hx.1
    refine ⟨x,G.carrier x,T.carrier x,hxp,hx.2,G.carrier_pos x,T.carrier_pos x,
      root_balance _ _ _ G.ha G.hd,root_balance _ _ _ T.ha T.hd,?_,?_,?_⟩
    · unfold residual Branch.flux at hres
      linarith
    · exact (G.service_iff qG x hqG hxp hcapG hmG).mpr ((le_max_left _ _).trans hx.1)
    · exact (T.service_iff qT x hqT hxp hcapT hmT).mpr ((le_max_right _ _).trans hx.1)

end
end CommonEnvironmentProtection.CoupledPrivate
