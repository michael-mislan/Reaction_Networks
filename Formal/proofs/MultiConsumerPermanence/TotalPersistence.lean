import proofs.MultiConsumerPermanence.Source
import proofs.MultiConsumerPermanence.LoadedPotential

namespace MultiConsumerPermanence
open CoreCouplingCAC CoreCouplingGlobal RobustPermanence Filter Topology Set

noncomputable def totalFloor (n : ℕ) : ℝ :=
  (1/4:ℝ)/(2*(((n:ℝ)+60000000)*Real.exp (150000*1000000))) *
    Real.exp (150000*(-1000000))

theorem totalFloor_pos (n : ℕ) : 0 < totalFloor n := by
  unfold totalFloor
  positivity

theorem aggregate_corrected_growth {n : ℕ} (e A B z H : ℝ) (x : Fin n → ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (hA : 0 ≤ A) (hA' : A ≤ 34)
    (hB : 2 ≤ B) (hB' : B ≤ 34) (hz : 0 ≤ z) (hz' : z ≤ 12)
    (hH : 0 ≤ H) (hH' : H ≤ 1536/7) (hx : ∀ i, 0 ≤ x i) :
    total x*(1/4-((n:ℝ)+60000000)*total x) ≤
      (z-1/2)*total x-(n:ℝ)*squares x-
        150000*total x*potentialRate e A B z H (total x) := by
  have h := consumer_corrected_growth e A B z H (total x) he he' hA hA'
    hB hB' hz hz' hH hH' (total_nonneg x hx)
  have hq := mul_le_mul_of_nonneg_left (squares_bounds x hx).1 (Nat.cast_nonneg n : (0:ℝ) ≤ n)
  nlinarith only [h,hq]

theorem total_eventually_upper {n : ℕ} (hn : 0 < n) (e : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (h : IsMultiTrajectory n e Y x) :
    ∀ᶠ t in atTop, total (x t) < 12 := by
  obtain ⟨T,hT⟩ := eventually_atTop.1
    (loaded_eventually_resident_absorbing e he he' Y _ h.toIsLoadedResidentTrajectory)
  apply eventual_upper_of_linear_drift (fun t => total (x t))
    (fun t => ((Y t).z-1/2)*total (x t)-(n:ℝ)*squares (x t))
    (max T 0) (2209/16) 12 12 (by norm_num) (by norm_num)
  · intro t ht
    exact total_hasDerivAt e Y x h t ((le_max_right _ _).trans ht)
  · intro t ht
    have h0 : 0 ≤ t := (le_max_right _ _).trans ht
    have hz := (hT t ((le_max_left _ _).trans ht)).2.2.1
    have hx := total_positive hn e Y x h t h0
    have hc := (squares_bounds (x t) (fun i => (h.consumer_positive t h0 i).le)).2
    have hh := mul_nonneg (by linarith : 0 ≤ 12-(Y t).z) hx.le
    nlinarith only [hh,hc,sq_nonneg (total (x t)-47/4)]

theorem total_eventually_lower {n : ℕ} (hn : 0 < n) (e : ℝ)
    (he : 0 ≤ e) (he' : e ≤ 1/50000) (Y : ℝ → State)
    (x : ℝ → Fin n → ℝ) (h : IsMultiTrajectory n e Y x) :
    ∀ᶠ t in atTop, totalFloor n < total (x t) := by
  obtain ⟨p⟩ := potentialPrimitives_nonempty e he he'
  let center := responsePotential e p 2 0 0 (2-responseTotal e 2)
  have habs := loaded_eventually_resident_absorbing e he he' Y _ h.toIsLoadedResidentTrajectory
  have hbox : ∀ᶠ t in atTop, 0 ≤ t ∧
      (Y t).A ∈ Icc (0:ℝ) 34 ∧ (Y t).B ∈ Icc (2:ℝ) 34 ∧
      (Y t).z ∈ Icc (0:ℝ) 12 ∧ (Y t).H ∈ Icc (0:ℝ) (1536/7) := by
    filter_upwards [habs,eventually_ge_atTop (0:ℝ)] with t ht h0
    have hp := h.positive t h0
    exact ⟨h0,⟨hp.1.le,by linarith [ht.1,hp.2.1]⟩,
      ⟨ht.2.2.2.le,by linarith [ht.1,hp.1]⟩,⟨hp.2.2.1.le,ht.2.2.1.le⟩,
      ⟨hp.2.2.2.le,by linarith [ht.2.1,hp.2.2.1]⟩⟩
  obtain ⟨T,hT⟩ := eventually_atTop.1 hbox
  apply bounded_corrector_eventual_floor (fun t => total (x t))
    (fun t => ((Y t).z-1/2)*total (x t)-(n:ℝ)*squares (x t))
    (fun t => trajectoryPotential e p Y t-center)
    (fun t => potentialRate e (Y t).A (Y t).B (Y t).z (Y t).H (total (x t)))
    T 150000 (1/4) ((n:ℝ)+60000000) (-1000000) 1000000
    (by norm_num) (by norm_num) (by positivity)
  · intro t ht
    exact total_positive hn e Y x h t (hT t ht).1
  · intro t ht
    obtain ⟨_,hA,hB,hz,hH⟩ := hT t ht
    exact abs_le.1 (uniform_potential_center_bound e p he he' _ _ _ _
      hA.1 hA.2 hB.1 hB.2 hz.1 hz.2 hH.1 hH.2)
  · intro t ht
    exact total_hasDerivAt e Y x h t (hT t ht).1
  · intro t ht
    obtain ⟨h0,_,hB,hz,hH⟩ := hT t ht
    exact (loaded_potential_hasDerivAt e p he he' Y _ h.toIsLoadedResidentTrajectory
      t h0 hB hz hH).sub_const center
  · intro t ht
    obtain ⟨h0,hA,hB,hz,hH⟩ := hT t ht
    exact aggregate_corrected_growth e _ _ _ _ _ he he' hA.1 hA.2 hB.1 hB.2
      hz.1 hz.2 hH.1 hH.2 (fun i => (h.consumer_positive t h0 i).le)

end MultiConsumerPermanence
