import proofs.CoreCouplingGlobal.RoutedSigns

namespace CoreCouplingGlobal
open CoreCouplingCAC Set

theorem routed_poly_continuous (e g : ℝ) : Continuous (routedPoly e g) := by
  unfold routedPoly routedNumerA routedDen routedK
  fun_prop

/-- A full parameter rectangle, not a sampled continuation or a boundary-only example. -/
theorem routed_region_three (e g : ℝ) (he : 0 ≤ e) (heu : e ≤ 1/50000)
    (hg : (999/1000:ℝ) ≤ g) (hgu : g ≤ 1) :
    ∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
      RoutedStationary e g x ∧ RoutedStationary e g y ∧ RoutedStationary e g w ∧
      x.z < y.z ∧ y.z < w.z ∧
      x.z ∈ Icc (9/10:ℝ) (11/10) ∧ y.z ∈ Icc (19/10:ℝ) (21/10) ∧
      w.z ∈ Icc (29/10:ℝ) (31/10) := by
  have h₁ := routed_sign_lowLeft e g he heu hg hgu
  have h₂ := routed_sign_lowRight e g he heu hg hgu
  have h₃ := routed_sign_midLeft e g he heu hg hgu
  have h₄ := routed_sign_midRight e g he heu hg hgu
  have h₅ := routed_sign_highLeft e g he heu hg hgu
  have h₆ := routed_sign_highRight e g he heu hg hgu
  obtain ⟨a,ha,hpa⟩ := intermediate_value_Icc
    (by norm_num : (9/10:ℝ) ≤ 11/10) (routed_poly_continuous e g).continuousOn
    (show (0:ℝ) ∈ Icc (routedPoly e g (9/10)) (routedPoly e g (11/10)) by
      constructor <;> linarith)
  obtain ⟨b,hb,hpb⟩ := intermediate_value_Icc'
    (by norm_num : (19/10:ℝ) ≤ 21/10) (routed_poly_continuous e g).continuousOn
    (show (0:ℝ) ∈ Icc (routedPoly e g (21/10)) (routedPoly e g (19/10)) by
      constructor <;> linarith)
  obtain ⟨c,hc,hpc⟩ := intermediate_value_Icc
    (by norm_num : (29/10:ℝ) ≤ 31/10) (routed_poly_continuous e g).continuousOn
    (show (0:ℝ) ∈ Icc (routedPoly e g (29/10)) (routedPoly e g (31/10)) by
      constructor <;> linarith)
  have ha' : a ∈ Icc (9/10:ℝ) (31/10) := ⟨ha.1,by linarith [ha.2]⟩
  have hb' : b ∈ Icc (9/10:ℝ) (31/10) := ⟨by linarith [hb.1],by linarith [hb.2]⟩
  have hc' : c ∈ Icc (9/10:ℝ) (31/10) := ⟨by linarith [hc.1],hc.2⟩
  have hgp : 0 < g := by linarith
  have hd : ∀ z ∈ Icc (9/10:ℝ) (31/10), routedDen g z ≠ 0 := by
    intro z hz
    have hgz := mul_pos hgp (show 0 < z by linarith [hz.1])
    dsimp [routedDen]
    linarith
  refine ⟨routedLift g a,routedLift g b,routedLift g c,
    routed_lift_positive g a hg hgu ha',routed_lift_positive g b hg hgu hb',
    routed_lift_positive g c hg hgu hc',
    routed_lift_stationary e g a (ne_of_gt hgp) (hd a ha') hpa,
    routed_lift_stationary e g b (ne_of_gt hgp) (hd b hb') hpb,
    routed_lift_stationary e g c (ne_of_gt hgp) (hd c hc') hpc,?_,?_,ha,hb,hc⟩
  · change a < b
    linarith [ha.2,hb.1]
  · change b < c
    linarith [hb.2,hc.1]

/-- Every point in this nonempty open rectangle has at least three positive
coupled equilibria, while the same intrinsic e has one under route isolation. -/
theorem routed_open_region_creation (e g : ℝ)
    (he : e ∈ Ioo (1/200000:ℝ) (1/50000))
    (hg : g ∈ Ioo (999/1000:ℝ) 1) :
    (∃! x : State, x.Positive ∧ RoutedStationary e 0 x) ∧
    ∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
      RoutedStationary e g x ∧ RoutedStationary e g y ∧ RoutedStationary e g w ∧
      x.z < y.z ∧ y.z < w.z := by
  obtain ⟨x,y,w,hx,hy,hw,hsx,hsy,hsw,hxy,hyw,_⟩ :=
    routed_region_three e g (by linarith [he.1]) he.2.le hg.1.le hg.2.le
  exact ⟨(routed_stationary_creation e he.1.le he.2.le).1,
    x,y,w,hx,hy,hw,hsx,hsy,hsw,hxy,hyw⟩

def routedCreationRegion : Set (ℝ × ℝ) :=
  Ioo (1/200000:ℝ) (1/50000) ×ˢ Ioo (999/1000:ℝ) 1

theorem routed_creation_region_open_nonempty :
    IsOpen routedCreationRegion ∧ routedCreationRegion.Nonempty := by
  refine ⟨isOpen_Ioo.prod isOpen_Ioo,⟨(1/100000,1999/2000),?_⟩⟩
  norm_num [routedCreationRegion]

theorem routed_creation_throughout_open_region (p : ℝ × ℝ)
    (hp : p ∈ routedCreationRegion) :
    (∃! x : State, x.Positive ∧ RoutedStationary p.1 0 x) ∧
    ∃ x y w : State, x.Positive ∧ y.Positive ∧ w.Positive ∧
      RoutedStationary p.1 p.2 x ∧ RoutedStationary p.1 p.2 y ∧
      RoutedStationary p.1 p.2 w ∧ x.z < y.z ∧ y.z < w.z :=
  routed_open_region_creation p.1 p.2 hp.1 hp.2

end CoreCouplingGlobal
