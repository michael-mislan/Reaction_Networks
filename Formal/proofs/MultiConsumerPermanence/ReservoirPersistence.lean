import proofs.MultiConsumerPermanence.ReservoirBounds

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence Filter Topology Set

noncomputable def reservoirWeight (dmin : ℝ) : ℝ := 288/dmin
noncomputable def reservoirTotalFloor (n : ℕ) (dmin : ℝ) : ℝ :=
  (1/8:ℝ)/(2*(((n:ℝ)+120000000+3*reservoirWeight dmin)*
    Real.exp (150000*(1000000+reservoirWeight dmin/300000)))) *
    Real.exp (150000*(-1000000))

theorem reservoirTotalFloor_pos (n : ℕ) (dmin : ℝ) (hdmin : 0 < dmin) :
    0 < reservoirTotalFloor n dmin := by
  dsimp [reservoirTotalFloor,reservoirWeight]
  positivity

theorem reservoir_aggregate_corrected_growth {n : ℕ} (e A B z H R d dmin : ℝ)
    (x : Fin n → ℝ) (hdmin : 0 < dmin) (hd : dmin ≤ d)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (hA : 0 ≤ A) (hA' : A ≤ 34)
    (hB : 2 ≤ B) (hB' : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 12)
    (hH : 0 ≤ H) (hH' : H ≤ 1536/7) (hR : 0 ≤ R) (hR' : R ≤ 2)
    (hx : ∀ i, 0 ≤ x i) :
    total x*(1/8-((n:ℝ)+120000000+3*reservoirWeight dmin)*total x) ≤
      (R*z-1/2)*total x-(n:ℝ)*squares x-
        150000*total x*(potentialRate e A B z H (R*total x)+
          (reservoirWeight dmin/150000)*((R-1)*(d-d*R-R*z*total x))) := by
  let D := dissipation (A+B-responseTotal e B) (60-(2+z)*B)
    (responseTotal e B-(1+z)*B-16*z-4*z^2+3*H)
    (16*z+2*z^2-(20001/10000)*H)
  have hD : 0 ≤ D := dissipation_nonneg _ _ _ _
  have hgap : z ≤ 3/4 → 529/103640000 ≤ D := fun hlow =>
    residual_gap _ _ _ _ (low_resource_separation e B z H he he' hB hB' hz hlow)
  have hg := corrected_boundary_growth z D hz hD hgap
  have hS := total_nonneg x hx
  have hv := consumer_potential_dissipation e A B z H (R*total x) he he' hA hA'
    hB hB' hz hz' hH hH' (mul_nonneg hR hS)
  have hp : (R-1)*(d-d*R-R*z*total x) ≤ -dmin*(R-1)^2+(12/4)*total x := by
    have hh := reservoir_potential_drift R z (total x) d 12 hz hz' hS
    have hdq := mul_le_mul_of_nonneg_right hd (sq_nonneg (R-1))
    nlinarith only [hh,hdq]
  have hb : 0 ≤ reservoirWeight dmin := by dsimp [reservoirWeight]; positivity
  have hbd : reservoirWeight dmin*dmin = 2*(12:ℝ)^2 := by
    dsimp [reservoirWeight]
    field_simp
    norm_num
  have hc := reservoir_corrected_growth R z 12 (total x) D
    (potentialRate e A B z H (R*total x)) ((R-1)*(d-d*R-R*z*total x))
    (reservoirWeight dmin) dmin hR' hz hz' hS hb hbd hg (by simpa only [D,mul_assoc] using hv) hp
  have hcs := mul_le_mul_of_nonneg_right hc hS
  have hq := mul_le_mul_of_nonneg_left (squares_bounds x hx).1 (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  nlinarith only [hcs,hq]

theorem reservoir_total_lower {n : ℕ} (hn : 0 < n) (e d dmin : ℝ)
    (hdmin : 0 < dmin) (hd : dmin ≤ d) (he : 0 ≤ e) (he' : e ≤ 1/50000)
    (Y : ℝ → State) (x : ℝ → Fin n → ℝ) (R : ℝ → ℝ)
    (h : IsReservoirTrajectory n e d d Y x R) :
    ∀ᶠ t in atTop, reservoirTotalFloor n dmin < total (x t) := by
  obtain ⟨p⟩ := potentialPrimitives_nonempty e he he'
  let center := responsePotential e p 2 0 0 (2-responseTotal e 2)
  have hb : 0 ≤ reservoirWeight dmin := by dsimp [reservoirWeight]; positivity
  have habs := loaded_eventually_resident_absorbing e he he' Y _ h.toIsLoadedResidentTrajectory
  have hr := reservoir_eventually_upper e d (lt_of_lt_of_le hdmin hd) Y x R h
  have hbox : ∀ᶠ t in atTop, 0 ≤ t ∧
      (Y t).A ∈ Icc (0:ℝ) 34 ∧ (Y t).B ∈ Icc (2:ℝ) 34 ∧
      (Y t).z ∈ Icc (0:ℝ) 12 ∧ (Y t).H ∈ Icc (0:ℝ) (1536/7) ∧
      R t ∈ Icc (0:ℝ) 2 := by
    filter_upwards [habs,hr,eventually_ge_atTop (0:ℝ)] with t ht hR h0
    have hp := h.positive t h0
    exact ⟨h0,⟨hp.1.le,by linarith [ht.1,hp.2.1]⟩,
      ⟨ht.2.2.2.le,by linarith [ht.1,hp.1]⟩,⟨hp.2.2.1.le,ht.2.2.1.le⟩,
      ⟨hp.2.2.2.le,by linarith [ht.2.1,hp.2.2.1]⟩,
      ⟨(h.reservoir_positive t h0).le,hR.le⟩⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hbox
  apply bounded_corrector_eventual_floor (fun t => total (x t))
    (fun t => (R t*(Y t).z-1/2)*total (x t)-(n:ℝ)*squares (x t))
    (fun t => trajectoryPotential e p Y t-center+
      (reservoirWeight dmin/150000)*reservoirPotential (R t))
    (fun t => potentialRate e (Y t).A (Y t).B (Y t).z (Y t).H (R t*total (x t))+
      (reservoirWeight dmin/150000)*((R t-1)*(d-d*R t-R t*(Y t).z*total (x t))))
    T 150000 (1/8) ((n:ℝ)+120000000+3*reservoirWeight dmin)
    (-1000000) (1000000+reservoirWeight dmin/300000)
    (by norm_num) (by norm_num) (by positivity)
  · intro t ht
    exact reservoir_total_positive hn e d d Y x R h t (hT t ht).1
  · intro t ht
    obtain ⟨_,hA,hB,hz,hH,hR⟩ := hT t ht
    have hv := abs_le.1 (uniform_potential_center_bound e p he he' _ _ _ _
      hA.1 hA.2 hB.1 hB.2 hz.1 hz.2 hH.1 hH.2)
    have hp := reservoir_potential_bounds (R t) hR.1 hR.2
    have hp0 := mul_nonneg hb hp.1
    have hp1 := mul_le_mul_of_nonneg_left hp.2 hb
    constructor <;> dsimp [trajectoryPotential,center] at * <;> linarith only [hv.1,hv.2,hp0,hp1]
  · intro t ht
    exact reservoir_total_deriv e d d Y x R h t (hT t ht).1
  · intro t ht
    obtain ⟨h0,_,hB,hz,hH,_⟩ := hT t ht
    exact ((loaded_potential_hasDerivAt e p he he' Y _ h.toIsLoadedResidentTrajectory
      t h0 hB hz hH).sub_const center).add
      ((reservoir_potential_hasDerivAt R t _ (h.dR t h0)).const_mul (reservoirWeight dmin/150000))
  · intro t ht
    obtain ⟨h0,hA,hB,hz,hH,hR⟩ := hT t ht
    exact reservoir_aggregate_corrected_growth e _ _ _ _ _ d dmin _ hdmin hd he he'
      hA.1 hA.2 hB.1 hB.2 hz.1 hz.2 hH.1 hH.2 hR.1 hR.2
      (fun i => (h.consumer_positive t h0 i).le)

end MultiConsumerPermanence
