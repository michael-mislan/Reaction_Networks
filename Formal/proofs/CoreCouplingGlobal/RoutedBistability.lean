import proofs.CoreCouplingGlobal.RoutedStableCenters
import proofs.CoreCouplingGlobal.RoutedLocalSelection
import proofs.CoreCouplingGlobal.RoutedAdmissibility

open Filter Topology
namespace CoreCouplingGlobal
open CoreCouplingCAC Set

def RoutedSelected (e g : ℝ) (L R : Fin 4 → ℝ) (c : State) : Prop :=
  ∀ x₀ : State, Near c x₀ →
    (∃ X : ℝ → State, X 0 = x₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt (fun s => coordinates (X s))
        (routedDerivative (flagshipRates e) g (X t)) t ∧ (X t).Positive ∧
        energy L R (transform c) (transform (X t)) ≤
          energy L R (transform c) (transform x₀)*Real.exp (-(1/100:ℝ)*t)) ∧
      Tendsto (fun t => coordinates (X t)) atTop (𝓝 (coordinates c))) ∧
    (∀ Y : ℝ → State, Y 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt (fun s => coordinates (Y s))
        (routedDerivative (flagshipRates e) g (Y t)) t) →
      Tendsto (fun t => coordinates (Y t)) atTop (𝓝 (coordinates c)))

theorem routedLow_selected (e g : ℝ)
    (he : (999/100000000:ℝ) ≤ e) (heu : e ≤ 1001/100000000)
    (hg : (999999/1000000:ℝ) ≤ g) (hgu : g ≤ 1)
    (c : State) (hc : InBox c routedLowRootLower routedLowRootUpper)
    (hs : RoutedStationary e g c) : RoutedSelected e g lowLeft lowRight c := by
  have hsub := routedLow_energy_inBox
  have hcbox : InBox c routedLowLower routedLowUpper :=
    hsub c c hc (by simp [energy])
  have hdec : ∀ x, InBox x routedLowLower routedLowUpper →
      routedEnergyRate e g lowLeft lowRight (transform c) (transform x) ≤
        -(1/100:ℝ)*energy lowLeft lowRight (transform c) (transform x) := by
    intro x hx
    have hm := routedLow_jacobian_domination e g he heu hg hgu (midpointState x c)
      (midpoint_inBox x c routedLowLower routedLowUpper hx hcbox)
    rw [midpoint_transform] at hm
    exact routed_nonlinear_energy_bound e g routedLowComparison lowLeft lowRight
      (transform c) (transform x) (1/100)
      low_comparison_certificate.2.1 low_comparison_certificate.1
      (routed_stationary_transformed e g c hs) hm.1 hm.2 routedLow_energy_row
  intro x₀ hx₀
  have h0 := low_near_energy c x₀ hx₀
  constructor
  · obtain ⟨X,hX0,hX,hlim⟩ := routed_local_selection e g lowLeft lowRight c
      routedLowLower routedLowUpper low_weight_lower (fun x hx => hsub x c hc hx)
      routedLow_box_norm routedLow_box_positive hdec x₀ h0
    exact ⟨X,hX0,fun t ht => ⟨(hX t ht).1,(hX t ht).2.1,(hX t ht).2.2.2⟩,hlim⟩
  · intro Y hY0 hY
    exact (routed_all_local_solutions_converge e g lowLeft lowRight c
      routedLowLower routedLowUpper low_weight_lower (fun x hx => hsub x c hc hx)
      hdec Y hY (by simpa only [hY0] using h0)).2

theorem routedHigh_selected (e g : ℝ)
    (he : (999/100000000:ℝ) ≤ e) (heu : e ≤ 1001/100000000)
    (hg : (999999/1000000:ℝ) ≤ g) (hgu : g ≤ 1)
    (c : State) (hc : InBox c routedHighRootLower routedHighRootUpper)
    (hs : RoutedStationary e g c) : RoutedSelected e g highLeft highRight c := by
  have hsub := routedHigh_energy_inBox
  have hcbox : InBox c routedHighLower routedHighUpper :=
    hsub c c hc (by simp [energy])
  have hdec : ∀ x, InBox x routedHighLower routedHighUpper →
      routedEnergyRate e g highLeft highRight (transform c) (transform x) ≤
        -(1/100:ℝ)*energy highLeft highRight (transform c) (transform x) := by
    intro x hx
    have hm := routedHigh_jacobian_domination e g he heu hg hgu (midpointState x c)
      (midpoint_inBox x c routedHighLower routedHighUpper hx hcbox)
    rw [midpoint_transform] at hm
    exact routed_nonlinear_energy_bound e g routedHighComparison highLeft highRight
      (transform c) (transform x) (1/100)
      high_comparison_certificate.2.1 high_comparison_certificate.1
      (routed_stationary_transformed e g c hs) hm.1 hm.2 routedHigh_energy_row
  intro x₀ hx₀
  have h0 := high_near_energy c x₀ hx₀
  constructor
  · obtain ⟨X,hX0,hX,hlim⟩ := routed_local_selection e g highLeft highRight c
      routedHighLower routedHighUpper high_weight_lower (fun x hx => hsub x c hc hx)
      routedHigh_box_norm routedHigh_box_positive hdec x₀ h0
    exact ⟨X,hX0,fun t ht => ⟨(hX t ht).1,(hX t ht).2.1,(hX t ht).2.2.2⟩,hlim⟩
  · intro Y hY0 hY
    exact (routed_all_local_solutions_converge e g highLeft highRight c
      routedHighLower routedHighUpper high_weight_lower (fun x hx => hsub x c hc hx)
      hdec Y hY (by simpa only [hY0] using h0)).2

def routedBistableRegion : Set (ℝ × ℝ) :=
  Ioo (999/100000000:ℝ) (1001/100000000) ×ˢ Ioo (999999/1000000:ℝ) 1

theorem routed_bistable_region_open_nonempty :
    IsOpen routedBistableRegion ∧ routedBistableRegion.Nonempty := by
  refine ⟨isOpen_Ioo.prod isOpen_Ioo,⟨(1/100000,1999999/2000000),?_⟩⟩
  norm_num [routedBistableRegion]

/-- Robust causal bistability: two actual attracting neighborhoods in an admissible
coupled family with uniquely stationary isolated modules and fixed fork capacity. -/
theorem routed_causal_bistability (e g : ℝ) (hp : (e,g) ∈ routedBistableRegion) :
    RoutedCoreCertificate e g ∧
    (∃! x : State, x.Positive ∧ RoutedStationary e 0 x) ∧
    ∃ x y : State, x.Positive ∧ y.Positive ∧ RoutedStationary e g x ∧
      RoutedStationary e g y ∧ x.z < y.z ∧
      RoutedSelected e g lowLeft lowRight x ∧ RoutedSelected e g highLeft highRight y := by
  obtain ⟨he,heu⟩ := hp.1
  obtain ⟨hg,hgu⟩ := hp.2
  have hewide : e ∈ Ioo (1/200000:ℝ) (1/50000) := ⟨by linarith,by linarith⟩
  have hgwide : g ∈ Ioo (999/1000:ℝ) 1 := ⟨by linarith,hgu⟩
  obtain ⟨x,hx,hsx,hcx⟩ := routedLow_center_exists e g he.le heu.le hg.le hgu.le
  obtain ⟨y,hy,hsy,hcy⟩ := routedHigh_center_exists e g he.le heu.le hg.le hgu.le
  have hzx := hcx.2.2.2.2.2.1
  have hzy := hcy.2.2.2.2.1
  norm_num [routedLowRootUpper,routedHighRootLower] at hzx hzy
  exact ⟨routed_core_certificate e g hewide hgwide,
    (routed_open_region_creation e g hewide hgwide).1,x,y,hx,hy,hsx,hsy,by linarith,
    routedLow_selected e g he.le heu.le hg.le hgu.le x hcx hsx,
    routedHigh_selected e g he.le heu.le hg.le hgu.le y hcy hsy⟩

end CoreCouplingGlobal
